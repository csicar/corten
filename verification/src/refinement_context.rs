

use rustc_hir as hir;

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
      if let CtxEntry::Typed {ident, ty} = entry {
        if  hir==ident {
          Some(ty.clone())
        } else {
          None
        }
      } else {
        None
      }
    })
  }
}

fn encode_refinement_context<'a>(ctx: RContext<'a>) -> String {
    ctx.entries
        .iter()
        .map(|entry| entry.encode_smt())
        .collect::<Vec<_>>()
        .join("\n")
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

impl<'a> CtxEntry<'a> {
    fn encode_smt(&self) -> String {
        match self {
            CtxEntry::Formula { expr } => refinements::encode_smt(expr),
            CtxEntry::Typed { ident: _, ty: _ } => format!("XXX"),
        }
    }
}
