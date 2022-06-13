use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
    io::Write,
};

use crate::{hir_ext::ExprExt, refinements::rename_ref_in_expr, smtlib_ext::SmtResExt};
use hir::ExprKind;
use quote::{format_ident, quote};
use rsmt2::Solver;
use rustc_hir as hir;
use rustc_hir_pretty::id_to_string;
use rustc_middle::ty::{TyCtxt, TypeckResults};
use std::fmt::Debug;
use std::hash::Hash;
use syn::parse_quote;
use tracing::{instrument, trace};

use itertools::Itertools;

use anyhow::anyhow;

use crate::refinements::{self, RefinementType};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RContext<'tcx, K: Debug + Eq + Hash + Display + SmtFmt = hir::HirId> {
    /// stack of formulas
    formulas: Vec<syn::Expr>,
    /// Association of variable declarations (K) with their current refinement type binder (String)
    binders: HashMap<K, String>,
    /// Association of the refinement type binder with the associated type
    types: HashMap<String, RefinementType<'tcx>>,
}

impl<'a, K> RContext<'a, K>
where
    K: Debug + Eq + Hash + Display + SmtFmt + Clone,
{
    pub fn new() -> RContext<'a> {
        RContext {
            formulas: Vec::new(),
            types: HashMap::new(),
            binders: HashMap::new(),
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

    pub fn update_ty(&mut self, hir: K, ty: RefinementType<'a>) {
        self.binders.remove(&hir);
        self.add_ty(hir, ty);
    }

    pub fn add_ty(&mut self, hir: K, ty: RefinementType<'a>) {
        assert!(!self.binders.contains_key(&hir));
        self.binders.insert(hir, ty.binder.clone());
        self.types.insert(ty.binder.clone(), ty);
    }

    pub fn rename_binders(&self, renamer: &impl Fn(&str) -> String) -> anyhow::Result<Self> {
        let binder_names: HashMap<&String, String> = self
            .binders
            .iter()
            .map(|(_, name)| (name, renamer(name)))
            .collect();
        let formulas = self
            .formulas
            .iter()
            .map(|formula| {
                rename_ref_in_expr(formula, renamer)
            })
            .try_collect()?;
        let binders = self
            .binders
            .iter()
            .map(|(hir_id, old_name)| 
                anyhow::Ok((
                    hir_id.clone(),
                    binder_names
                        .get(old_name)
                        .ok_or(anyhow!("name not found in binders list"))?
                        .clone(),
                ))
            )
            .try_collect()?;
        let types = self.types.iter().map(|(k, v)| {
            let new_name = renamer(k);
            assert_eq!(k, &v.binder);
            anyhow::Ok((new_name, v.rename_binders(renamer)?))
        }).try_collect()?;
        anyhow::Ok(RContext {
            formulas,
            binders,
            types,
        })
    }

    pub fn lookup_hir(&self, hir: &K) -> Option<RefinementType<'a>> {
        self.binders
            .get(&hir)
            .and_then(|binder| self.types.get(binder))
            .map(|entry| entry.clone())
        // self.types.get(&hir).map(|entry| entry.clone())
    }

    pub fn encode_smt<P>(&self, solver: &mut Solver<P>, tcx: &TyCtxt<'a>) -> anyhow::Result<()> {
        solver.comment("<Context>").into_anyhow()?;
        solver.push(1).into_anyhow()?;

        self.encode_binder_decls(solver, tcx)?;
        self.encode_predicates(solver)?;
        self.encode_formulas(solver)?;

        trace!("done encode_smt context");
        solver.comment("</Context>").into_anyhow()?;
        Ok(())
    }

    pub fn loopup_decl_for_binder(&self, needle: &str) -> Option<&K> {
        self.binders
            .iter()
            .find_map(|(key, binder)| if binder == needle { Some(key) } else { None })
    }

    pub fn encode_binder_decl<P>(
        &self,
        solver: &mut Solver<P>,
        ty: &RefinementType<'a>,
        tcx: &TyCtxt<'a>,
    ) -> anyhow::Result<()> {
        let ident = self
            .loopup_decl_for_binder(&ty.binder)
            .map(|decl| decl.fmt_str(tcx))
            .unwrap_or("<dangling type>".to_string());
        solver
            .comment(&format!("decl for {}", ident))
            .into_anyhow()?;

        fn encode_type<'tcx>(ty: &rustc_middle::ty::Ty<'tcx>) -> &'static str {
            match ty.kind() {
                rustc_middle::ty::TyKind::Bool => "Bool",
                rustc_middle::ty::TyKind::Char => todo!(),
                rustc_middle::ty::TyKind::Int(_) => "Int", // todo: respect size
                rustc_middle::ty::TyKind::Uint(_) => "Int", // Todo respect unsigned
                rustc_middle::ty::TyKind::Ref(_region, ref_type, _mut) => encode_type(ref_type),
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
            .try_for_each(|(ident, ty)| self.encode_binder_decl(solver, ty, tcx))?;
        Ok(())
    }

    pub fn encode_predicates<P>(&self, solver: &mut Solver<P>) -> anyhow::Result<()> {
        self.types.iter().try_for_each(|(binder, ty)| {
            let decl_name = match self.loopup_decl_for_binder(binder) {
                Some(hir_id) => hir_id.to_string(),
                None => "<dangling type>".to_string(),
            };
            solver
                .comment(&format!("predicate for {}: {}", binder, decl_name))
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

    pub fn with_tcx<'b, 'c>(&'a self, tcx: &'b TyCtxt<'c>) -> FormatContext<'b, 'a, 'c, K> {
        FormatContext { ctx: self, tcx }
    }

    /// Tries to construct a RefoinementContext from a `assert_ctx` call.
    /// The call should look like this:
    /// ```
    /// assert_ctx(&["b > 0"], &[(&my_var, { "i" }, {"i > 0"}), ((), {"a"}, {"a == 2"})])
    /// ```
    /// Where [`func_decl`] is "assert_ctx" and [`func_args`] are its args
    /// A unit type as the first entry in the refinement association list denotes a dangling
    /// refinemen type
    pub fn try_from_assert_expr(
        func_decl: &hir::Node<'a>,
        func_args: &[hir::Expr<'a>],
        tcx: &TyCtxt<'a>,
        local_ctx: &TypeckResults<'a>,
    ) -> anyhow::Result<Option<RContext<'a, hir::HirId>>> {
        if func_decl.ident().map(|v| v.name.to_string()) == Some("assert_ctx".to_string()) {
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
                                let var = match &var_raw.kind {
                                    ExprKind::AddrOf(_, _, inner) => {
                                        let decl = inner.try_into_path_hir_id(tcx, local_ctx)?;
                                        anyhow::Ok(Some(decl))
                                    }
                                    ExprKind::Tup([]) => anyhow::Ok(None),
                                    _other => todo!(),
                                }?;
                                trace!(var=?var, binder=?binder, pred=?predicate);
                                let var_ty = local_ctx.node_type(
                                    var.expect("TODO: deal with type of dangling refinements"),
                                );
                                anyhow::Ok((
                                    var,
                                    RefinementType {
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
                    let binders: HashMap<hir::HirId, String> = refinement_symbols
                        .iter()
                        .filter_map(|(maybe_hir, rt)| {
                            if let Some(hir) = maybe_hir {
                                Some((hir.clone(), rt.binder.clone()))
                            } else {
                                None
                            }
                        })
                        .collect::<HashMap<_, _>>();
                    let types: HashMap<String, RefinementType> = refinement_symbols
                        .into_iter()
                        .map(|(_, rt)| (rt.binder.clone(), rt))
                        .collect();

                    anyhow::Ok(Some(RContext {
                        formulas: form_symbols,
                        binders,
                        types,
                    }))
                }
                _other => todo!(),
            }
        } else {
            anyhow::Ok(None)
        }
    }
}

#[instrument(skip_all, ret)]
pub fn is_sub_context<'tcx, 'a, K: Debug + Eq + Hash + Display + SmtFmt + Clone, P>(
    super_ctx: &RContext<'tcx, K>,
    sub_ctx: &RContext<'tcx, K>,
    tcx: &TyCtxt<'tcx>,
    solver: &mut Solver<P>,
) -> anyhow::Result<()> {
    let super_ctx = super_ctx.rename_binders(&|name| format!("super_{}", name))?;
    let sub_ctx = sub_ctx.rename_binders(&|name| format!("sub_{}", name))?;

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
        anyhow::bail!("super ctx may contain at most the same declarations as the super ctx")
    }

    sub_ctx.encode_binder_decls(solver, tcx)?;
    super_ctx.encode_binder_decls(solver, tcx)?;

    sub_ctx.types.iter().try_for_each(|(binder, sub_ty)| {
        // sub_ctx.encode_binder_decl(solver, &sub_ty, tcx)?;

        // the super ctx may be missing some declarations, that are contained in the
        // sub_ctx.
        match sub_ctx
            .loopup_decl_for_binder(binder)
            .and_then(|hir_id| super_ctx.lookup_hir(hir_id))
        {
            // In case there is a matching super_ty => encode and equate them
            Some(super_ty) => {
                let sub_binder = format_ident!("{}", &sub_ty.binder);
                let super_binder = format_ident!("{}", &super_ty.binder);
                solver
                    .comment(&format!("same hir id => equate"))
                    .into_anyhow()?;
                solver
                    .assert(refinements::encode_smt(
                        &parse_quote! { #sub_binder == #super_binder },
                    ))
                    .into_anyhow()?;
            }
            // When there is no super_ty matching, nothing else to do
            None => {}
        }

        anyhow::Ok(())
    })?;
    sub_ctx.encode_predicates(solver)?;
    sub_ctx.encode_formulas(solver)?;

    solver.comment("<SuperCtx>").into_anyhow()?;

    let super_term = super_ctx
        .types
        .iter()
        .map(|(_, ty)| refinements::encode_smt(&ty.predicate))
        .chain(
            super_ctx
                .formulas
                .iter()
                .map(|formula| refinements::encode_smt(formula)),
        )
        .collect::<Vec<_>>()
        .join("\n    ");
    solver
        .assert(&format!("(not (and true {}))", super_term))
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

pub struct FormatContext<'a, 'b, 'c, K: Debug + Eq + Hash + Display + SmtFmt> {
    ctx: &'a RContext<'b, K>,
    tcx: &'a TyCtxt<'c>,
}

pub trait SmtFmt {
    fn fmt_str<'tcx>(&self, tcx: &TyCtxt<'tcx>) -> String;
}

impl SmtFmt for hir::HirId {
    fn fmt_str<'tcx>(&self, tcx: &TyCtxt<'tcx>) -> String {
        let node_str = tcx.hir().node_to_string(*self);
        let span = tcx.hir().span(self.clone()).data();
        format!("{:?} {}", span, node_str)
    }
}

impl<'a, 'b, 'c, K: SmtFmt + Debug + Eq + Hash + Display + SmtFmt + Clone> Display
    for FormatContext<'a, 'b, 'c, K>
{
    fn fmt<'tcx>(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "RContext {{")?;
        writeln!(f, "    // formulas")?;
        for formula in &self.ctx.formulas {
            writeln!(f, "    {}", quote! { #formula })?;
        }
        writeln!(f, "    // types")?;
        for (binder, ty) in &self.ctx.types {
            let decl = self.ctx.loopup_decl_for_binder(binder);
            let name = match decl {
                Some(id) => id.fmt_str(self.tcx),
                None => "<dangling>".to_string(),
            };
            writeln!(f, "    {} : {}", name, ty)?;
        }
        writeln!(f, "}}")
    }
}
