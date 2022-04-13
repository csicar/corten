
use rsmt2::{Solver};
use rustc_hir as hir;
use tracing::trace;
use crate::smtlib_ext::SmtResExt;

use crate::refinements::{self, RefinementType};

#[derive(Debug, Clone)]
pub struct RContext<'a> {
    entries: Vec<CtxEntry<'a>>,
}

impl<'a> RContext<'a> {
    pub fn new() -> RContext<'a> {
        RContext { entries: vec![] }
    }

    pub fn add_entry(&mut self, entry: CtxEntry<'a>) {
        self.entries.push(entry)
    }

    pub fn lookup_hir<'b>(&self, hir: &hir::HirId) -> Option<RefinementType<'a>> {
        self.entries.iter().find_map(|entry| {
            if let CtxEntry::Typed { ident, ty } = entry {
                if hir == ident {
                    Some(ty.clone())
                } else {
                    None
                }
            } else {
                None
            }
        })
    }

    pub fn encode_smt<P>(&self, solver: &mut Solver<P>) -> anyhow::Result<()> {
        solver.comment("<Context>").into_anyhow()?;
        solver.push(1).into_anyhow()?;
        self.entries.iter().try_for_each(|entry| match entry {
            CtxEntry::Typed { ident: _, ty } => {
                solver
                    .declare_const(&ty.binder, "Int")
                    .into_anyhow()?;
                solver
                    .assert(refinements::encode_smt(&ty.predicate))
                    .into_anyhow()?;
                anyhow::Ok(())
            }
            CtxEntry::Formula { expr } => {
                solver
                    .assert(refinements::encode_smt(expr))
                    .into_anyhow()?;

                anyhow::Ok(())
            }
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
