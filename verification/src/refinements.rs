use crate::hir_ext::TyExt;
use anyhow::anyhow;
use rustc_hir as hir;
use rustc_middle::ty as middle;
use rustc_middle::ty::{self, Ty, TyCtxt, TypeckResults};

#[derive(Debug)]
pub struct RefinementType<'a> {
    pub base: Ty<'a>,
    pub binder: String,
    pub predicate: syn::Expr,
}

fn parse_predicate(raw_predicate: &str) -> anyhow::Result<syn::Expr> {
    let parsed = syn::parse_str::<syn::Expr>(raw_predicate)?;
    Ok(parsed)
}

pub fn extract_refinement_from_type_alias<'a, 'tcx>(
    raw_type: &'a hir::Ty<'a>,
    tcx: &'a TyCtxt<'tcx>,
    local_ctx: &'a TypeckResults<'a>,
) -> anyhow::Result<(String, syn::Expr)> {
    if let Some((base, binder, raw_predicate)) = raw_type.try_into_refinement(tcx) {
        let predicate = parse_predicate(raw_predicate.as_str())?;
        Ok((binder.as_str().to_string(), predicate))
    } else {
        Err(anyhow!(
            "type {:?} does not seem to be a refinement type, when one was expected",
            raw_type
        ))
    }
}
