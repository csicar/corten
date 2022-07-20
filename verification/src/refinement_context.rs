use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
    io::Write,
};

use crate::{
    hir_ext::ExprExt,
    refinements::{rename_ref_in_expr, vars_in_expr, ReferenceRefinement, RefinementType},
    smtlib_ext::SmtResExt,
};
use hir::ExprKind;
use quote::quote;
use rsmt2::Solver;
use rustc_hir as hir;

use rustc_middle::ty::{TyCtxt, TypeckResults};
use std::fmt::Debug;
use std::hash::Hash;

use tracing::{info, instrument, trace};

use itertools::Itertools;

use anyhow::anyhow;

use crate::refinements::{self, PredicateRefinement};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum TyId {
    // Represents a associated type that is referencing another decl (HirId)
    Ref(ReferenceRefinement),
    // Represents an associated type that references a logical variable
    LogicVar(String),
}

impl TyId {
    fn map_logic_var(self, f: impl FnOnce(String) -> String) -> Self {
        match self {
            TyId::Ref(_) => self,
            TyId::LogicVar(i) => TyId::LogicVar(f(i)),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RContext<'tcx> {
    /// stack of path conditions
    formulas: Vec<syn::Expr>,

    /// Association of variable declarations with their current refinement type. This can either be:
    /// - a lvar
    /// - or a reference refinement
    binders: HashMap<hir::HirId, TyId>,

    /// Set of all PredicateRefinement in current context.
    types: HashSet<PredicateRefinement<'tcx>>,
}

impl<'a> RContext<'a> {
    pub fn new() -> RContext<'a> {
        RContext {
            formulas: Vec::new(),
            binders: HashMap::new(),
            types: HashSet::new(),
        }
    }

    pub fn push_formula(&mut self, formula: syn::Expr) {
        self.formulas.push(formula);
    }

    pub fn pop_formula(&self) -> Self {
        let mut formulas = self.formulas.clone();
        formulas.pop().unwrap();
        RContext {
            formulas,
            binders: self.binders.clone(),
            types: self.types.clone(),
        }
    }

    pub fn update_ty(&mut self, hir: hir::HirId, ty: RefinementType<'a>) {
        use RefinementType::*;
        // update should never change the rust base type.
        // But changing from Predicate Type to Reference Type or vice versa would change
        // the base type ==> Forbid!
        match (&ty, self.lookup_hir(&hir)) {
            (PredicateType { .. }, Some(PredicateType { .. })) => {
                //ok
            }
            (ReferenceType { .. }, Some(ReferenceType { .. })) => {
                //ok
            }
            _ => panic!(),
        };
        self.binders.remove(&hir);
        self.add_ty(hir, ty);
        // self.garbage_collect();
    }

    pub fn add_ty(&mut self, hir: hir::HirId, ty: RefinementType<'a>) {
        assert!(!self.binders.contains_key(&hir));
        match ty {
            RefinementType::PredicateType { kind } => {
                let binder = kind.binder.clone();
                self.types.insert(kind);
                self.binders.insert(hir, TyId::LogicVar(binder));
            }
            RefinementType::ReferenceType { kind } => {
                self.binders.insert(hir, TyId::Ref(kind));
            }
        }
    }

    /// Changes the logic vars names according to renamer:
    /// `ctx! { _2 > 2; a |-> a1 > 0, b |-> b1 == a1 }`.rename_logic_vars(|name| name + "_new")
    /// `ctx! { _2_new > 2; a |-> a1_new > 0, b |-> b1_new == a1_new }`
    pub fn rename_logic_vars(&self, renamer: &impl Fn(&str) -> String) -> anyhow::Result<Self> {
        let formulas = self
            .formulas
            .iter()
            .map(|formula| rename_ref_in_expr(formula, renamer))
            .try_collect()?;
        let binders = self
            .binders
            .iter()
            .map(|(hir_id, ty_id)| {
                anyhow::Ok((
                    hir_id.clone(),
                    ty_id.clone().map_logic_var(|old_name| renamer(&old_name)),
                ))
            })
            .try_collect()?;
        let types = self
            .types
            .iter()
            .map(|v| anyhow::Ok(v.rename_binders(renamer)?))
            .try_collect()?;
        anyhow::Ok(RContext {
            formulas,
            binders,
            types,
        })
    }

    pub fn lookup_logic_var(&self, logic_var: &str) -> Option<PredicateRefinement<'a>> {
        self.types
            .iter()
            .find(|pred_ty| pred_ty.binder == logic_var)
            .cloned()
    }

    pub fn lookup_hir(&self, hir: &hir::HirId) -> Option<RefinementType<'a>> {
        self.binders.get(hir).and_then(|ty_id| match ty_id {
            TyId::Ref(r) => Some(RefinementType::from(r.clone())),
            TyId::LogicVar(lvar) => self.lookup_logic_var(lvar).map(|p| p.into()),
        })
    }

    /// Find the logic variable belonging to `hir`. For reference types, this will return
    /// the referenced hir's logic var!
    pub fn lookup_binder_for_hir(&self, hir: &hir::HirId) -> Option<String> {
        self.lookup_hir(hir).and_then(|ty| match ty {
            RefinementType::PredicateType { kind } => Some(kind.binder),
            RefinementType::ReferenceType { kind } => self.lookup_binder_for_hir(&kind.destination),
        })
    }

    pub fn encode_smt<P>(&self, solver: &mut Solver<P>, tcx: &TyCtxt<'a>) -> anyhow::Result<()> {
        solver.comment("<Context>").into_anyhow()?;
        solver.push(1).into_anyhow()?;

        self.encode_binder_decls(solver, tcx)?;
        self.encode_predicates(solver, tcx)?;
        self.encode_formulas(solver)?;

        trace!("done encode_smt context");
        solver.comment("</Context>").into_anyhow()?;
        Ok(())
    }

    pub fn origin_label_for_binder<'b, 'c: 'b, 'd>(
        &self,
        ty: &'b PredicateRefinement,
        tcx: &'c TyCtxt<'d>,
    ) -> String {
        let associated_decl = self.binders.iter().find_map(|(hir_id, ty_id)| match ty_id {
            TyId::LogicVar(logic_var) if &ty.binder == logic_var => Some(hir_id.fmt_str(tcx)),
            _ => None,
        });
        associated_decl.unwrap_or("<dangling type>".to_string())
    }

    pub fn origin_label_for_binders<'b>(
        &'b self,
        tcx: &TyCtxt<'a>,
    ) -> HashMap<&'b PredicateRefinement, String> {
        self.types
            .iter()
            .map(|ty| (ty, self.origin_label_for_binder(ty, tcx)))
            .collect::<HashMap<_, _>>()
    }

    pub fn encode_binder_decl<P>(
        &self,
        solver: &mut Solver<P>,
        ty: &PredicateRefinement<'a>,
        tcx: &TyCtxt<'a>,
    ) -> anyhow::Result<()> {
        let ident = self.origin_label_for_binder(ty, tcx);
        solver
            .comment(&format!("decl for {}", ident))
            .into_anyhow()?;

        fn encode_type<'tcx>(ty: &rustc_middle::ty::Ty<'tcx>) -> String {
            match ty.kind() {
                rustc_middle::ty::TyKind::Bool => "Bool".to_string(),
                rustc_middle::ty::TyKind::Char => todo!(),
                rustc_middle::ty::TyKind::Int(_) => "Int".to_string(), // todo: respect size
                rustc_middle::ty::TyKind::Uint(_) => "Int".to_string(), // Todo respect unsigned
                rustc_middle::ty::TyKind::Ref(_region, ref_type, _mut) => encode_type(ref_type),
                rustc_middle::ty::TyKind::Slice(inner_ty) => {
                    format!("(Array Int {})", encode_type(inner_ty))
                }
                other => todo!("don't know how to encode ty {:?} in smt", other),
            }
        }

        let smt_ty = encode_type(&ty.base);

        solver.declare_const(&ty.binder, smt_ty).into_anyhow()?;
        Ok(())
    }

    pub fn encode_binder_decls<P>(
        &self,
        solver: &mut Solver<P>,
        tcx: &TyCtxt<'a>,
    ) -> anyhow::Result<()> {
        self.types
            .iter()
            .try_for_each(|ty| self.encode_binder_decl(solver, ty, tcx))?;
        Ok(())
    }

    pub fn encode_predicates<P>(
        &self,
        solver: &mut Solver<P>,
        tcx: &TyCtxt<'a>,
    ) -> anyhow::Result<()> {
        self.types.iter().try_for_each(|ty| {
            let decl_name = self.origin_label_for_binder(ty, tcx);
            solver
                .comment(&format!("predicate for {}: {}", ty.binder, decl_name))
                .into_anyhow()?;
            solver
                .assert(refinements::encode_smt(&ty.predicate))
                .into_anyhow()?;
            anyhow::Ok(())
        })?;

        Ok(())
    }

    pub fn encode_formulas<P>(&self, solver: &mut Solver<P>) -> anyhow::Result<()> {
        self.formulas.iter().try_for_each(|expr| {
            solver.assert(refinements::encode_smt(expr)).into_anyhow()?;

            anyhow::Ok(())
        })?;
        Ok(())
    }

    pub fn with_tcx<'b, 'c>(&'a self, tcx: &'b TyCtxt<'c>) -> FormatContext<'b, 'a, 'c> {
        FormatContext { ctx: self, tcx }
    }

    // #[instrument]
    // pub fn garbage_collect(&mut self) {
    //     let mut live_variables: HashSet<String> = self
    //         .binders
    //         .values()
    //         .cloned()
    //         .chain(self.formulas.iter().flat_map(vars_in_expr))
    //         .collect();

    //     loop {
    //         let new_vars: HashSet<String> = live_variables
    //             .iter()
    //             .flat_map(|var| self.types.get(var).unwrap().free_vars())
    //             .collect();

    //         trace!("live_variables {live_variables:#?}, referenced variables {new_vars:#?}");

    //         if new_vars.is_subset(&live_variables) {
    //             break;
    //         }

    //         live_variables = live_variables.union(&new_vars).cloned().collect();
    //     }

    //     self.types.retain(|k, _| live_variables.contains(k));
    //     trace!(types=%self.types.values().map(|k| k.to_string()).collect::<String>(), "new types:")
    // }

    /// Tries to construct a RefinementContext from a `assert_ctx` or `update_ctx` call.
    /// The call should look like this:
    /// ```
    /// assert_ctx(&["b > 0"], &[(&my_var, { "i" }, {"i > 0"}), ((&other_var,), {"a"}, {"a == 2"})])
    /// ```
    /// Where [`func_args`] are `assert_ctx`'s args
    /// A unit type as the first entry in the refinement association list denotes a dangling
    /// refinement type
    pub fn try_from_assert_expr(
        func_args: &[hir::Expr<'a>],
        tcx: &TyCtxt<'a>,
        local_ctx: &TypeckResults<'a>,
    ) -> anyhow::Result<RContext<'a>> {
        match func_args {
            [hir::Expr {
                kind:
                    ExprKind::AddrOf(
                        hir::BorrowKind::Ref,
                        hir::Mutability::Not,
                        hir::Expr {
                            kind: ExprKind::Array(forms_raw),
                            ..
                        },
                    ),
                ..
            }, hir::Expr {
                kind:
                    ExprKind::AddrOf(
                        hir::BorrowKind::Ref,
                        hir::Mutability::Not,
                        hir::Expr {
                            kind: ExprKind::Array(refinements_raw),
                            ..
                        },
                    ),
                ..
            }] => {
                let form_symbols: Vec<syn::Expr> = forms_raw
                    .iter()
                    .map(|arg| {
                        arg.try_into_symbol()
                            .map(|sym| sym.to_string())
                            .ok_or(anyhow!("not a symbol"))
                            .and_then(|s| refinements::parse_predicate(&s))
                    })
                    .try_collect()?;
                let refinement_symbols: Vec<(_, _)> = refinements_raw
                    .iter()
                    .map(|arg| {
                        if let ExprKind::Tup([var_raw, binder_raw, pred_raw]) = arg.kind {
                            let binder = binder_raw
                                .try_into_symbol()
                                .map(|sym| sym.to_string())
                                .ok_or(anyhow!("unexpected thing in place of binder"))?;
                            let predicate = pred_raw
                                .try_into_symbol()
                                .map(|sym| sym.to_string())
                                .ok_or(anyhow!("unexpected thing in place of pred"))?;
                            trace!(?var_raw);
                            let (var, var_ty) = match &var_raw.kind {
                                // dangling reference?
                                ExprKind::AddrOf(
                                    _,
                                    _,
                                    hir::Expr {
                                        kind: ExprKind::Tup([inner]),
                                        ..
                                    },
                                ) => {
                                    let decl = inner.try_into_path_hir_id(tcx, local_ctx)?;
                                    let ty = local_ctx.node_type(decl);
                                    anyhow::Ok((None, ty))
                                }
                                // normal reference?
                                ExprKind::AddrOf(_, _, inner) => {
                                    let decl = inner.try_into_path_hir_id(tcx, local_ctx)?;
                                    let ty = local_ctx.node_type(decl);
                                    anyhow::Ok((Some(decl), ty))
                                }
                                _other => todo!(),
                            }?;
                            trace!(var=?var, binder=?binder, pred=?predicate);
                            anyhow::Ok((
                                var,
                                PredicateRefinement {
                                    base: var_ty,
                                    binder,
                                    predicate: refinements::parse_predicate(&predicate)?,
                                },
                            ))
                        } else {
                            anyhow::bail!("not a tuple")
                        }
                    })
                    .try_collect()?;
                let binders: HashMap<hir::HirId, TyId> = refinement_symbols
                    .iter()
                    .filter_map(|(maybe_hir, rt)| {
                        if let Some(hir) = maybe_hir {
                            Some((hir.clone(), TyId::LogicVar(rt.binder.clone())))
                        } else {
                            None
                        }
                    })
                    .collect::<HashMap<_, _>>();
                let types: HashSet<PredicateRefinement> =
                    refinement_symbols.into_iter().map(|(_, rt)| rt).collect();

                anyhow::Ok(RContext {
                    formulas: form_symbols,
                    binders,
                    types,
                })
            }
            _other => todo!(),
        }
    }
}

#[instrument(skip_all, ret)]
pub fn is_sub_context<'tcx, 'a, P>(
    super_ctx: &RContext<'tcx>,
    sub_ctx: &RContext<'tcx>,
    tcx: &TyCtxt<'tcx>,
    solver: &mut Solver<P>,
) -> anyhow::Result<()> {
    trace!(super_ctx=%(super_ctx.with_tcx(tcx)), sub_ctx=%(sub_ctx.with_tcx(tcx)), "check");
    solver
        .comment("checking is_sub_context ...")
        .into_anyhow()?;
    solver.push(1).into_anyhow()?;

    if super_ctx
        .binders
        .keys()
        .collect::<HashSet<_>>()
        .is_subset(&sub_ctx.binders.keys().collect::<HashSet<_>>())
    {
        //every thing is fine
    } else {
        anyhow::bail!("super ctx may contain at most the same declarations as the sub ctx")
    }

    // sub_ctx.encode_binder_decls(solver, tcx)?;
    // super_ctx.encode_binder_decls(solver, tcx)?;

    let super_binder = &super_ctx.types;
    let sub_binder = &sub_ctx.types;
    super_binder.union(&sub_binder).try_for_each(|ty| {
        if let Some(sub_ty) = sub_ctx.lookup_logic_var(&ty.binder) {
            sub_ctx.encode_binder_decl(solver, &sub_ty, tcx)?;
        } else if let Some(super_ty) = super_ctx.lookup_logic_var(&ty.binder) {
            super_ctx.encode_binder_decl(solver, &super_ty, tcx)?;
        } else {
            panic!("union is not a union?")
        }
        anyhow::Ok(())
    })?;
    // info!(?sub_binder, ?super_binder);
    // super_binder
    //     .intersection(&sub_binder)
    //     .try_for_each(|binder| {
    //         let sub_binder = format_ident!("sub_{}", binder);
    //         let super_binder = format_ident!("super_{}", binder);
    //         solver
    //             .assert(refinements::encode_smt(&parse_quote! {
    //                 #sub_binder == #super_binder
    //             }))
    //             .into_anyhow()
    //     })?;

    let sub_decls = sub_ctx
        .binders
        .iter()
        .map(|(hir_id, _)| hir_id)
        .collect::<HashSet<_>>();

    let super_decls = super_ctx
        .binders
        .iter()
        .map(|(key, _)| key)
        .collect::<HashSet<_>>();

    // Maps sub binder to their hir_id-corresponding super binder
    let intersection_binder = sub_decls
        .intersection(&super_decls)
        .map(|hir_id| {
            let sub_binder = sub_ctx
                .lookup_binder_for_hir(hir_id)
                .expect("sub_ctx must contain hir_id, b/c of intersection");
            let super_binder = super_ctx
                .lookup_binder_for_hir(hir_id)
                .expect("super_ctx must contain hir_id, b/c of intersection");

            (super_binder, sub_binder)
        })
        .collect::<HashMap<_, _>>();
    trace!(?intersection_binder);
    let intersection_renamed_super_ctx = super_ctx.rename_logic_vars(&|old_name| {
        intersection_binder
            .get(old_name)
            .cloned()
            .unwrap_or_else(|| old_name.to_string())
    })?;

    info!(intersection_ctx=%intersection_renamed_super_ctx.with_tcx(tcx));

    // solver
    //     .comment("formulas from intersection {")
    //     .into_anyhow()?;
    // intersection_renamed_sub_ctx.encode_formulas(solver)?;
    // solver.comment("}").into_anyhow()?;

    // solver
    //     .comment("predicate from intersection {")
    //     .into_anyhow()?;
    // intersection_renamed_sub_ctx.encode_predicates(solver)?;
    // solver.comment("}").into_anyhow()?;

    solver
        .comment("left-over binders from sub_ctx {")
        .into_anyhow()?;
    sub_ctx.encode_formulas(solver)?;
    sub_ctx.encode_predicates(solver, tcx)?;
    solver.comment("}").into_anyhow()?;

    // sub_ctx.types.iter().try_for_each(|(binder, sub_ty)| {
    //     // sub_ctx.encode_binder_decl(solver, &sub_ty, tcx)?;

    //     // the super ctx may be missing some declarations, that are contained in the
    //     // sub_ctx.
    //     match sub_ctx
    //         .loopup_decl_for_binder(binder)
    //         .and_then(|hir_id| super_ctx.lookup_hir(hir_id))
    //     {
    //         // In case there is a matching super_ty => encode and equate them
    //         Some(super_ty) => {
    //             let sub_binder = format_ident!("{}", &sub_ty.binder);
    //             let super_binder = format_ident!("{}", &super_ty.binder);
    //             solver
    //                 .comment(&format!("same hir id => equate"))
    //                 .into_anyhow()?;
    //             solver
    //                 .assert(refinements::encode_smt(
    //                     &parse_quote! { #sub_binder == #super_binder },
    //                 ))
    //                 .into_anyhow()?;
    //         }
    //         // When there is no super_ty matching, nothing else to do
    //         None => {}
    //     }

    //     anyhow::Ok(())
    // })?;
    // sub_ctx.encode_predicates(solver)?;
    // sub_ctx.encode_formulas(solver)?;

    solver.comment("<SuperCtx>").into_anyhow()?;

    let super_term = intersection_renamed_super_ctx
        .types
        .iter()
        .map(|ty| refinements::encode_smt(&ty.predicate))
        .chain(
            intersection_renamed_super_ctx
                .formulas
                .iter()
                .map(refinements::encode_smt),
        )
        .collect::<Vec<_>>()
        .join("\n       ");
    solver
        .assert(&format!("(not (and true \n       {}\n    ))", super_term))
        .into_anyhow()?;

    solver.comment("</SuperCtx>").into_anyhow()?;

    solver
        .comment(&format!(
            "checking: {} ≼  {}",
            sub_ctx.with_tcx(tcx),
            super_ctx.with_tcx(tcx)
        ))
        .into_anyhow()?;
    solver.flush()?;
    let is_sat = solver.check_sat().into_anyhow()?;
    solver
        .comment(&format!("done checking is_sub_context! is sat: {}", is_sat))
        .into_anyhow()?;
    solver.pop(1).into_anyhow()?;
    if is_sat {
        Err(anyhow::anyhow!(
            "{} is not a sub context of {}, which is required here",
            sub_ctx.with_tcx(tcx),
            super_ctx.with_tcx(tcx)
        ))
    } else {
        anyhow::Ok(())
    }
}

pub struct FormatContext<'a, 'b, 'c> {
    ctx: &'a RContext<'b>,
    tcx: &'a TyCtxt<'c>,
}

pub trait SmtFmt {
    fn fmt_str<'tcx>(&self, tcx: &TyCtxt<'tcx>) -> String;
}

impl SmtFmt for hir::HirId {
    fn fmt_str<'tcx>(&self, tcx: &TyCtxt<'tcx>) -> String {
        let node_str = tcx.hir().node_to_string(*self);
        let span = tcx.hir().span(*self).data();
        format!("{:?} {}", span, node_str)
    }
}

impl SmtFmt for &str {
    fn fmt_str<'tcx>(&self, _tcx: &TyCtxt<'tcx>) -> String {
        format!("{:?}", self)
    }
}

impl<'a, 'b, 'c> Display for FormatContext<'a, 'b, 'c> {
    fn fmt<'tcx>(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "RContext {{")?;
        writeln!(f, "    // formulas")?;
        for formula in &self.ctx.formulas {
            writeln!(f, "    {}", quote! { #formula })?;
        }
        writeln!(f, "    // types")?;
        for ty in self
            .ctx
            .types
            .iter()
            .sorted_by(|key_a, key_b| key_a.binder.cmp(&key_b.binder))
        {
            let name = self.ctx.origin_label_for_binder(ty, self.tcx);
            writeln!(f, "    {} : {}", name, ty)?;
        }
        writeln!(f, "}}")
    }
}
