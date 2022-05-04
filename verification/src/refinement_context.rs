use std::{collections::HashMap, fmt::Display};

use crate::smtlib_ext::SmtResExt;
use rsmt2::Solver;
use rustc_hir as hir;
use rustc_hir_pretty::id_to_string;
use rustc_middle::ty::TyCtxt;
use tracing::trace;

use crate::refinements::{self, RefinementType};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RContext<'tcx> {
    formulas: Vec<syn::Expr>,
    types: HashMap<hir::HirId, RefinementType<'tcx>>,
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
        self.types.iter().try_for_each(|(ident, ty)| {
            solver.comment(&format!("decl for {}", ident)).into_anyhow()?;
            solver.declare_const(&ty.binder, "Int").into_anyhow()?;
            anyhow::Ok(())
        })?;
        self.types.iter().try_for_each(|(ident, ty)| {
            solver.comment(&format!("predicate for {} {}", ty.binder, ident)).into_anyhow()?;
            solver
                .assert(refinements::encode_smt(&ty.predicate))
                .into_anyhow()?;
            anyhow::Ok(())
        })?;
        self.formulas.iter().try_for_each(|expr| {
            solver.assert(refinements::encode_smt(expr)).into_anyhow()?;

            anyhow::Ok(())
        })?;
        trace!("done encode_smt context");
        solver.comment("</Context>").into_anyhow()?;
        Ok(())
    }

    #[cfg(test)]
    pub fn with_tcx<'b, 'c>(&'a self, tcx: &'b TyCtxt<'c>) -> FormatContext<'b, 'a, 'c>{
        FormatContext { ctx: self, tcx}
    }
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
