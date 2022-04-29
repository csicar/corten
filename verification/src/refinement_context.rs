use std::collections::HashMap;

use crate::smtlib_ext::SmtResExt;
use rsmt2::Solver;
use rustc_hir as hir;
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
            solver.declare_const(&ty.binder, "Int").into_anyhow()?;
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
}

#[derive(Debug, Clone)]
pub enum CtxEntry<'a> {
    Typed {
        ident: hir::HirId,
        ty: RefinementType<'a>,
    },
    Formula {
        expr: syn::Expr,
    },
}
