use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
    io::Write,
};

use crate::{
    hir_ext::ExprExt,
    refinements::{rename_ref_in_expr, vars_in_expr},
    smtlib_ext::{SmtResExt, SolverExt},
};
use hir::{ExprKind, HirId};
use quote::quote;
use rsmt2::Solver;
use rustc_hir as hir;

use rustc_middle::ty::{TyCtxt, TypeckResults};
use std::fmt::Debug;
use std::hash::Hash;

use tracing::{error, info, instrument, trace};

use itertools::Itertools;

use anyhow::anyhow;

use crate::refinements::{self, RefinementType};

/// Represents the entity, that a type should be attached to. There are two options:
/// - attach to a definition site (i.e. hir id)
///     For `let a = 2`, we attach `ty!{==2}` to hir id of a
/// - attach to a anonymous location (i.e. an argument)
///     For `fn(a: &mut ty!{ v : i32 | v == 2 })` we attach
///     - `ty!{ == &a}` to `Definition(<a's hir id>)`
///     - `ty!{==2}` to `Anonymous(<a's hir id>)`
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeTarget<K> {
    Definition(K),
    /// Anonymous Definition, which is referenced by `.0`
    /// In general targetting a location by a reference is problematic, because we might
    /// overlook aliasing to that location.
    /// `Anonymous` may only be used for parameters. They are known to be non aliased (inside the current scope)
    Anonymous(usize),
}

impl<K> TypeTarget<K> {
    fn map<K2>(self, f: &impl Fn(K) -> K2) -> TypeTarget<K2> {
        match self {
            TypeTarget::Definition(d) => TypeTarget::Definition(f(d)),
            TypeTarget::Anonymous(id) => TypeTarget::Anonymous(id),
        }
    }
}

impl<K: SmtFmt> SmtFmt for TypeTarget<K> {
    fn fmt_str<'tcx>(&self, tcx: &TyCtxt<'tcx>) -> String {
        match self {
            TypeTarget::Definition(d) => d.fmt_str(tcx),
            TypeTarget::Anonymous(d) => format!("<anon decl from argument {}>", d),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RContext<'tcx, K: Debug + Eq + Hash + Display + SmtFmt = hir::HirId> {
    /// stack of formulas
    formulas: Vec<syn::Expr>,

    /// Association of variable declarations (K) with their current refinement type binder (String)
    binders: HashMap<TypeTarget<K>, String>,

    /// Association of program variables and their hir ids
    /// E.g. for `ty!{ v: &mut i32 | v == &a }` we need to know what the identifier `a` belongs to the hir id of `a`
    reference_destinations: HashMap<String, TypeTarget<K>>,

    /// Association of the refinement type binder with the associated type
    types: HashMap<String, RefinementType<'tcx>>,
}

impl<'a, K> RContext<'a, K>
where
    K: Debug + Eq + Hash + Display + SmtFmt + Clone,
{
    pub fn new() -> RContext<'a, K> {
        RContext {
            formulas: Vec::new(),
            types: HashMap::new(),
            reference_destinations: HashMap::new(),
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
            reference_destinations: self.reference_destinations.clone(),
            types: self.types.clone(),
        }
    }

    pub fn assume_formula(&self, formula: syn::Expr) -> Self {
        let formulas = vec![formula]
            .into_iter()
            .chain(self.formulas.clone())
            .collect();
        RContext {
            formulas,
            binders: self.binders.clone(),
            reference_destinations: self.reference_destinations.clone(),
            types: self.types.clone(),
        }
    }

    pub fn update_ty(&mut self, target: TypeTarget<K>, ty: RefinementType<'a>) {
        self.binders.remove(&target);
        self.add_any_ty(target, ty);
        // self.garbage_collect();
    }

    fn add_any_ty(&mut self, def_hir_id: TypeTarget<K>, ty: RefinementType<'a>) {
        assert!(!self.binders.contains_key(&def_hir_id));
        self.binders.insert(def_hir_id, ty.binder.clone());
        self.types.insert(ty.binder.clone(), ty);
    }

    pub fn add_ty(&mut self, hir: K, ty: RefinementType<'a>) {
        let def_hir_id = TypeTarget::Definition(hir);
        self.add_any_ty(def_hir_id, ty)
    }

    pub fn add_argument_no(&mut self, number: usize, ty: RefinementType<'a>) {
        let def_hir_id = TypeTarget::Anonymous(number);
        self.add_any_ty(def_hir_id, ty)
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
            .map(|formula| rename_ref_in_expr(formula, renamer))
            .try_collect()?;
        let binders = self
            .binders
            .iter()
            .map(|(hir_id, old_name)| {
                anyhow::Ok((
                    hir_id.clone(),
                    binder_names
                        .get(old_name)
                        .ok_or_else(|| anyhow!("name not found in binders list"))?
                        .clone(),
                ))
            })
            .try_collect()?;
        let types_entries: Vec<_> = self
            .types
            .iter()
            .map(|(k, v)| {
                let new_name = renamer(k);
                assert_eq!(k, &v.binder);
                trace!("renamed {k} to {new_name}");
                anyhow::Ok((new_name, v.rename_binders(renamer)?))
            })
            .try_collect()?;
        // `types_entries` might have multiple enties for one key.
        // this happens if the renaming in not injective.
        let types = {
            let mut map = HashMap::new();
            types_entries.into_iter().for_each(|(k, v)| {
                let current_value: Option<RefinementType> = map.remove(&k);
                let new_value = match current_value {
                    None => v,
                    Some(pred) => pred.with_additional_predicate(v.predicate),
                };
                map.insert(k, new_value);
            });

            map
        };
        anyhow::Ok(RContext {
            formulas,
            binders,
            types,
            reference_destinations: self.reference_destinations.clone(),
        })
    }

    pub fn lookup_hir(&self, hir: &K) -> Option<RefinementType<'a>> {
        self.lookup_type_by_type_target(&TypeTarget::Definition(hir.clone()))
    }

    pub fn lookup_type_by_type_target(&self, target: &TypeTarget<K>) -> Option<RefinementType<'a>> {
        self.binders
            .get(target)
            .and_then(|binder| self.types.get(binder))
            .cloned()
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

    /// Get the Hir of the decl currently associated with the logic variable `needle`
    pub fn lookup_decl_for_binder(&self, needle: &str) -> Option<&TypeTarget<K>> {
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
            .lookup_decl_for_binder(&ty.binder)
            .map(|decl| decl.fmt_str(tcx))
            .unwrap_or_else(|| "<dangling type>".to_string());
        solver
            .comment(&format!("decl for {}", ident))
            .into_anyhow()?;

        fn encode_type(ty: &rustc_middle::ty::Ty) -> String {
            match ty.kind() {
                rustc_middle::ty::TyKind::Bool => "Bool".to_string(),
                rustc_middle::ty::TyKind::Char => todo!(),
                rustc_middle::ty::TyKind::Int(_) => "Int".to_string(), // todo: respect size
                rustc_middle::ty::TyKind::Uint(_) => "Int".to_string(), // Todo respect unsigned
                rustc_middle::ty::TyKind::Ref(_region, ref_type, _mut) => encode_type(ref_type),
                rustc_middle::ty::TyKind::Slice(inner_ty) => {
                    format!("(Array Int {})", encode_type(inner_ty))
                }
                rustc_middle::ty::TyKind::Tuple(fields) if fields.len() == 0 => "Unit".to_string(), // todo: respect size
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
            .try_for_each(|(_ident, ty)| self.encode_binder_decl(solver, ty, tcx))?;
        Ok(())
    }

    /// To encode a predicate `l == &p` to smt, we need to know the logic var associated with `p`
    /// `self.get_logic_var_for_reference_target(TypeTarget::Definition(p))` returns p's logic variable
    pub fn get_logic_var_for_reference_target(
        &self,
        target: &TypeTarget<syn::Ident>,
    ) -> Option<String> {
        trace!("target {:?}", target);
        let target = self.lookup_reference_dest(target).unwrap();
        trace!("has reference dst {:?}", target);
        self.binders
            .iter()
            .find(|(k, _)| k == &&target)
            // .unwrap_or_else(|| panic!("cannot find {:?} in binders: {:?}", target, self.binders))
            .map(|target| target.1.clone())
    }

    /// Get the reference destination described by `ty`' and its predicate in the ctx `self`.
    /// for a type { _2 | _2 == &x } return TypeTarget::Definition(x)
    /// for a type { _3 | _3 == _1 } in ctx {_1 == &y } return TypeTarget::Definition(x)
    pub fn get_reference_target_for_type(
        &self,
        ty: &RefinementType,
    ) -> anyhow::Result<TypeTarget<syn::Ident>> {
        RefinementType::get_reference_type_in_expr(&ty.predicate).or_else(|_| {
            let mut predicates: Vec<&syn::Expr> = self
                .types
                .iter()
                .map(|(_binder, ty)| &ty.predicate)
                .collect();
            predicates.push(&ty.predicate);
            Self::equivalence_set_for_logic_var(predicates, &ty.binder)
                .1
                .ok_or_else(|| anyhow!("could not find a reference target for type {}", ty))
        })
    }

    /// for a context { _1 == _2 && true, _2 == &x, _3 > 0 },
    /// self.equivalence_set_for_logic_var("_1") will return (set!["_1", "_2"], "x")
    #[instrument(skip_all, fields(?logic_var), ret)]
    fn equivalence_set_for_logic_var<'i>(
        predicates: Vec<&'i syn::Expr>,
        logic_var: &str,
    ) -> (HashSet<String>, Option<TypeTarget<syn::Ident>>) {
        fn equivalent_logic_vars_in_expr(
            equivalence_set: &mut HashSet<String>,
            equivalent_pvars: &mut HashSet<TypeTarget<syn::Ident>>,
            expr: &syn::Expr,
        ) {
            match expr {
                syn::Expr::Binary(syn::ExprBinary {
                    left,
                    op: syn::BinOp::And(_),
                    right,
                    ..
                }) => {
                    equivalent_logic_vars_in_expr(equivalence_set, equivalent_pvars, left);
                    equivalent_logic_vars_in_expr(equivalence_set, equivalent_pvars, right);
                }
                syn::Expr::Binary(syn::ExprBinary {
                    left:
                        box syn::Expr::Path(syn::ExprPath {
                            path: left_path, ..
                        }),
                    op: syn::BinOp::Eq(_),
                    right: box right,
                    ..
                }) => {
                    if let Some(left_name) = left_path.get_ident().map(syn::Ident::to_string) {
                        trace!("right side: {}", quote! {#right});
                        match right {
                            syn::Expr::Path(syn::ExprPath {
                                path: right_path, ..
                            }) => {
                                if let Some(right_name) =
                                    right_path.get_ident().map(syn::Ident::to_string)
                                {
                                    // matches ` _1 == b`

                                    if equivalence_set.contains(&left_name) {
                                        equivalence_set.insert(right_name);
                                    } else if equivalence_set.contains(&right_name) {
                                        equivalence_set.insert(left_name);
                                    }
                                }
                            }
                            _ => {
                                trace!(?equivalence_set, ?left_name, "im here ");
                                if equivalence_set.contains(&left_name) {
                                    trace!("im here");
                                    // matches `_1 == XXXX` if `_1` in equivalence set

                                    // try to match `_1 == &b`
                                    if let Ok(pvar) =
                                        RefinementType::get_reference_type_in_expr(expr)
                                    {
                                        trace!("im here");
                                        equivalent_pvars.insert(pvar);
                                    }
                                }
                            }
                        }
                    }
                }
                syn::Expr::Binary(_) => {}
                syn::Expr::Lit(_) => {}
                syn::Expr::Paren(syn::ExprParen { expr: box expr, .. }) => {
                    equivalent_logic_vars_in_expr(equivalence_set, equivalent_pvars, expr)
                }
                syn::Expr::Path(_) => {}
                syn::Expr::Reference(_) => {}
                syn::Expr::Unary(_) => {}
                _ => todo!(),
            }
        }
        let mut equivalence_set = HashSet::from([logic_var.to_string()]);
        let mut equivalent_pvars = HashSet::new();

        loop {
            let size_before = equivalence_set.len();

            for predicate in predicates.iter() {
                equivalent_logic_vars_in_expr(
                    &mut equivalence_set,
                    &mut equivalent_pvars,
                    &predicate,
                );
            }

            // reached fixed-point?b
            if size_before == equivalence_set.len() {
                break;
            }
        }
        assert!(
            equivalent_pvars.len() <= 1,
            "Only one program variable should be equivalent to any program var"
        );
        (equivalence_set, equivalent_pvars.into_iter().next())
    }

    pub fn encode_predicates<P>(&self, solver: &mut Solver<P>) -> anyhow::Result<()> {
        self.types.iter().try_for_each(|(binder, ty)| {
            let decl_name = match self.lookup_decl_for_binder(binder) {
                Some(TypeTarget::Definition(hir_id)) => hir_id.to_string(),
                Some(TypeTarget::Anonymous(hir_id)) => hir_id.to_string(),
                None => "<dangling type>".to_string(),
            };
            solver
                .comment(&format!("predicate for {}: {}", binder, decl_name))
                .into_anyhow()?;
            solver.comment(&format!("    {}", ty)).into_anyhow()?;
            solver
                .assert(refinements::encode_smt(&ty.predicate, &|target| {
                    self.get_logic_var_for_reference_target(target).unwrap()
                }))
                .into_anyhow()?;
            anyhow::Ok(())
        })?;

        Ok(())
    }

    pub fn encode_formulas<P>(&self, solver: &mut Solver<P>) -> anyhow::Result<()> {
        self.formulas.iter().try_for_each(|expr| {
            solver
                .assert(refinements::encode_smt(expr, &|target| {
                    self.get_logic_var_for_reference_target(target).unwrap()
                }))
                .into_anyhow()?;

            anyhow::Ok(())
        })?;
        Ok(())
    }

    pub fn with_tcx<'b, 'c>(&'a self, tcx: &'b TyCtxt<'c>) -> FormatContext<'b, 'a, 'c, K> {
        FormatContext { ctx: self, tcx }
    }

    #[instrument]
    pub fn garbage_collect(&mut self) {
        let mut live_variables: HashSet<String> = self
            .binders
            .values()
            .cloned()
            .chain(
                self.formulas
                    .iter()
                    .flat_map(|formula| vars_in_expr(formula)),
            )
            .collect();

        loop {
            let new_vars: HashSet<String> = live_variables
                .iter()
                .flat_map(|var| self.types.get(var).unwrap().free_vars())
                .collect();

            trace!("live_variables {live_variables:#?}, referenced variables {new_vars:#?}");

            if new_vars.is_subset(&live_variables) {
                break;
            }

            live_variables = live_variables.union(&new_vars).cloned().collect();
        }

        self.types.retain(|k, _| live_variables.contains(k));
        trace!(types=%self.types.values().map(|k| k.to_string()).collect::<String>(), "new types:")
    }

    pub fn add_reference_dest(&mut self, name: String, hir_id: TypeTarget<K>) {
        self.reference_destinations.insert(name, hir_id);
    }

    // Try to get the type target belonging to `target`
    // - For `a` if returns a's hir id
    // - For an anonymous target, it will return that target
    pub fn lookup_reference_dest(
        &self,
        target: &TypeTarget<syn::Ident>,
    ) -> anyhow::Result<TypeTarget<K>> {
        match target {
            TypeTarget::Definition(name) => self
                .reference_destinations
                .get(&name.to_string())
                .cloned()
                .ok_or_else(|| {
                    anyhow!(
                        "Missing {name} in reference destination set {:?}",
                        self.reference_destinations
                    )
                }),
            TypeTarget::Anonymous(arg_no) => Ok(TypeTarget::Anonymous(*arg_no)),
        }
    }

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
    ) -> anyhow::Result<RContext<'a, hir::HirId>> {
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
                let binders: HashMap<TypeTarget<HirId>, String> = refinement_symbols
                    .iter()
                    .filter_map(|(maybe_hir, rt)| {
                        if let Some(hir) = maybe_hir {
                            Some((TypeTarget::Definition(hir.clone()), rt.binder.clone()))
                        } else {
                            None
                        }
                    })
                    .collect::<HashMap<_, _>>();
                let types: HashMap<String, RefinementType> = refinement_symbols
                    .into_iter()
                    .map(|(_, rt)| (rt.binder.clone(), rt))
                    .collect();

                anyhow::Ok(RContext {
                    formulas: form_symbols,
                    binders,
                    types,
                    reference_destinations: HashMap::new(),
                })
            }
            _other => todo!(),
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
    trace!(super_ctx=%(super_ctx.with_tcx(tcx)), sub_ctx=%(sub_ctx.with_tcx(tcx)), "check");
    solver
        .comment("checking is_sub_context ...")
        .into_anyhow()?;
    solver.push(1).into_anyhow()?;
    solver.add_prelude().into_anyhow()?;

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

    let super_binder = super_ctx.types.keys().collect::<HashSet<_>>();
    let sub_binder = sub_ctx.types.keys().collect::<HashSet<_>>();
    super_binder.union(&sub_binder).try_for_each(|&binder| {
        if let Some(ty) = sub_ctx.types.get(binder) {
            sub_ctx.encode_binder_decl(solver, ty, tcx)?;
        } else if let Some(ty) = super_ctx.types.get(binder) {
            super_ctx.encode_binder_decl(solver, ty, tcx)?;
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
        .map(|target| {
            let sub_ty = sub_ctx
                .lookup_type_by_type_target(target)
                .expect("sub_ctx must contain target, b/c of intersection");
            let super_ty = super_ctx
                .lookup_type_by_type_target(target)
                .expect("super_ctx must contain target, b/c of intersection");

            (super_ty.binder, sub_ty.binder)
        })
        .collect::<HashMap<_, _>>();
    trace!(?intersection_binder);
    let intersection_renamed_super_ctx = super_ctx.rename_binders(&|old_name| {
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
    sub_ctx.encode_predicates(solver)?;
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
        .map(|(_, ty)| {
            refinements::encode_smt(&ty.predicate, &|target| {
                intersection_renamed_super_ctx
                    .get_logic_var_for_reference_target(target)
                    .unwrap()
            })
        })
        .chain(
            intersection_renamed_super_ctx
                .formulas
                .iter()
                .map(|formula| {
                    refinements::encode_smt(formula, &|target| {
                        intersection_renamed_super_ctx
                            .get_logic_var_for_reference_target(target)
                            .unwrap()
                    })
                }),
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

#[instrument(skip_all, fields(%sub_ty, %super_ty))]
pub fn require_is_subtype_of<'tcx, P>(
    sub_ty: &RefinementType<'tcx>,
    super_ty: &RefinementType<'tcx>,
    ctx: &RContext<'tcx>,
    tcx: &TyCtxt<'tcx>,
    solver: &mut Solver<P>,
) -> anyhow::Result<()> {
    info!(
        "need to do subtyping judgement: {} ≼  {} in ctx {}",
        sub_ty,
        super_ty,
        ctx.with_tcx(tcx)
    );
    solver.comment("checking is_subtype_of").into_anyhow()?;
    solver.push(1).into_anyhow()?;
    solver.add_prelude().into_anyhow()?;
    ctx.encode_smt(solver, tcx)?;

    if ctx.lookup_decl_for_binder(&sub_ty.binder).is_none() {
        solver.declare_const(&sub_ty.binder, "Int").into_anyhow()?;
    }
    solver
        .assert(refinements::encode_smt(&sub_ty.predicate, &|target| {
            ctx.get_logic_var_for_reference_target(target).unwrap()
        }))
        .into_anyhow()?;

    // solver
    //     .declare_const(&super_ty.binder, "Int")
    //     .into_anyhow()?;

    // solver
    //     .assert(format!("(= {} {})", &super_ty.binder, &sub_ty.binder))
    //     .into_anyhow()?;
    let renamed_super_ty = super_ty.rename_binder(&sub_ty.binder)?;

    solver
        .assert(format!(
            "(not {})",
            refinements::encode_smt(&renamed_super_ty.predicate, &|target| {
                ctx.get_logic_var_for_reference_target(target).unwrap()
            })
        ))
        .into_anyhow()?;

    solver
        .comment(&format!("checking: {} ≼  {}", sub_ty, super_ty))
        .into_anyhow()?;
    solver.flush()?;
    trace!("checking: {} ≼  {}", sub_ty, super_ty);
    let is_sat = solver.check_sat().into_anyhow()?;
    solver
        .comment(&format!("done checking is_subtype_of! is sat: {}", is_sat))
        .into_anyhow()?;

    solver.pop(2).into_anyhow()?;
    solver.comment(&"-".repeat(80)).into_anyhow()?;
    if is_sat {
        let msg = format!(
            "Subtyping judgement failed: {} is not a sub_ty of {}",
            &sub_ty, &super_ty
        );
        error!("{} in ctx {}", msg, ctx.with_tcx(tcx));
        Err(anyhow!(msg))
    } else {
        info!("no counterexample found 🮱");
        // no counterexample found => everything is fine => continue
        Ok(())
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

impl SmtFmt for &str {
    fn fmt_str<'tcx>(&self, _tcx: &TyCtxt<'tcx>) -> String {
        format!("{:?}", self)
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
        for (binder, ty) in self
            .ctx
            .types
            .iter()
            .sorted_by(|(key_a, _), (key_b, _)| key_a.cmp(key_b))
        {
            let decl = self.ctx.lookup_decl_for_binder(binder);
            let name = match decl {
                Some(id) => id.fmt_str(self.tcx),
                None => "<dangling>".to_string(),
            };
            writeln!(f, "    {} : {}", name, ty)?;
        }
        writeln!(f, "}}")
    }
}
