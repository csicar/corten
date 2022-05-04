use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
    io::Write,
};

use crate::smtlib_ext::SmtResExt;
use quote::{quote, format_ident};
use rsmt2::Solver;
use rustc_hir as hir;
use rustc_hir_pretty::id_to_string;
use rustc_middle::ty::TyCtxt;
use syn::parse_quote;
use tracing::trace;

use crate::refinements::{self, RefinementType};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RContext<'tcx> {
    pub formulas: Vec<syn::Expr>,
    pub types: HashMap<hir::HirId, RefinementType<'tcx>>,
}

impl<'a> RContext<'a> {
    pub fn new() -> RContext<'a> {
        RContext {
            formulas: Vec::new(),
            types: HashMap::new(),
        }
    }

    pub fn add_formula(&mut self, formula: syn::Expr) {
        self.formulas.push(formula);
    }

    pub fn update_ty(&mut self, hir: hir::HirId, ty: RefinementType<'a>) {
        self.types.remove(&hir);
        self.add_ty(hir, ty);
    }

    pub fn add_ty(&mut self, hir: hir::HirId, ty: RefinementType<'a>) {
        assert!(!self.types.contains_key(&hir));
        self.types.insert(hir, ty);
    }

    pub fn lookup_hir<'b>(&self, hir: &hir::HirId) -> Option<RefinementType<'a>> {
        self.types.get(&hir).map(|entry| entry.clone())
    }

    pub fn encode_smt<P>(&self, solver: &mut Solver<P>) -> anyhow::Result<()> {
        solver.comment("<Context>").into_anyhow()?;
        solver.push(1).into_anyhow()?;

        self.encode_declarations(solver)?;
        self.encode_predicates(solver)?;
        self.encode_formulas(solver)?;

        trace!("done encode_smt context");
        solver.comment("</Context>").into_anyhow()?;
        Ok(())
    }

    pub fn encode_declaration<P>(
        &self,
        solver: &mut Solver<P>,
        ident: &hir::HirId,
        ty: &RefinementType<'a>,
    ) -> anyhow::Result<()> {
        solver
            .comment(&format!("decl for {}", ident))
            .into_anyhow()?;
        solver.declare_const(&ty.binder, "Int").into_anyhow()?;
        Ok(())
    }

    pub fn encode_declarations<P>(&self, solver: &mut Solver<P>) -> anyhow::Result<()> {
        self.types.iter().try_for_each(|(ident, ty)| {
            self.encode_declaration(solver, ident, ty);
            anyhow::Ok(())
        })?;
        Ok(())
    }

    pub fn encode_predicates<P>(&self, solver: &mut Solver<P>) -> anyhow::Result<()> {
        self.types.iter().try_for_each(|(ident, ty)| {
            solver
                .comment(&format!("predicate for {} {}", ty.binder, ident))
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
}

pub fn is_sub_context<'tcx, 'a, P>(
    super_ctx: &RContext<'tcx>,
    sub_ctx: &RContext<'tcx>,
    tcx: &TyCtxt<'a>,
    solver: &mut Solver<P>,
) -> anyhow::Result<()> {
    solver.push(1).into_anyhow()?;

    assert_eq!(
        super_ctx.types.keys().collect::<HashSet<_>>(),
        sub_ctx.types.keys().collect::<HashSet<_>>()
    );

    super_ctx.types.iter().try_for_each(|(hir_id, super_ty)| {
        let sub_ty = sub_ctx.lookup_hir(hir_id).expect("missing expected hir");
        super_ctx.encode_declaration(solver, hir_id, super_ty)?;
        if super_ty.binder != sub_ty.binder {
            sub_ctx.encode_declaration(solver, hir_id, &sub_ty)?;

            let super_binder = format_ident!("{}", &super_ty.binder);
            let sub_binder = format_ident!("{}", &sub_ty.binder);
            solver.assert(refinements::encode_smt(&parse_quote!{ #sub_binder == #super_binder })).into_anyhow()?;
        }
        anyhow::Ok(())
    })?;
    sub_ctx.encode_predicates(solver)?;
    sub_ctx.encode_formulas(solver)?;

    solver.comment("<SuperCtx>").into_anyhow()?;

    
    let super_term = super_ctx.types.iter().map(|(_, ty)| {
        refinements::encode_smt(&ty.predicate)
    }).chain(super_ctx.formulas.iter().map(|formula| {
        refinements::encode_smt(formula)
    })).collect::<Vec<_>>().join("\n    ");
    solver.assert(&format!("(not (and {}))", super_term)).into_anyhow()?;

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
        .comment(&format!("done! is sat: {}", is_sat))
        .into_anyhow()?;
    solver.pop(1).into_anyhow()?;

    Ok(())
}

pub struct FormatContext<'a, 'b, 'c> {
    ctx: &'a RContext<'b>,
    tcx: &'a TyCtxt<'c>,
}

impl<'a, 'b, 'c> Display for FormatContext<'a, 'b, 'c> {
    fn fmt<'tcx>(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "RContext {{")?;
        writeln!(f, "// formulas")?;
        for formula in &self.ctx.formulas {
            writeln!(f, "   {:?}", formula)?;
        }
        writeln!(f, "// types")?;
        for (id, ty) in &self.ctx.types {
            let c = self.tcx.hir().node_to_string(*id);
            writeln!(f, "    {} : {}", c, ty)?;
        }
        writeln!(f, "}}")
    }
}
