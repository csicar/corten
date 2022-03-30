use crate::hir_ext::TyExt;
use rustc_hir::Ty;
use anyhow::anyhow;
use rustc_middle::ty::TyCtxt;


#[derive(Debug)]
pub struct RefinementType<'a> {
    pub base: &'a Ty<'a>,
    pub binder: String,
    pub predicate: syn::Expr,
}

fn parse_predicate(raw_predicate: &str) -> anyhow::Result<syn::Expr> {
    let parsed = syn::parse_str::<syn::Expr>(raw_predicate)?;
    Ok(parsed)
}

pub fn extract_refinement_type_from_type_alias<'a, 'tcx>(
    raw_type: &'a Ty<'a>,
    tcx: &'a TyCtxt<'tcx>,
) -> anyhow::Result<RefinementType<'a>> {
    if let Some((base, binder, raw_predicate)) = raw_type.try_into_refinement(tcx) {

      let predicate = parse_predicate(raw_predicate.as_str())?;
      Ok(RefinementType {
          base,
          predicate,
          binder: binder.as_str().to_string(),
      })
    } else {
      Err(anyhow!("type {:?} does not seem to be a refinement type, when one was expected", raw_type))
    }
}
