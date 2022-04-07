use crate::hir_ext::TyExt;
use anyhow::anyhow;
use rustc_hir as hir;

use core::fmt::Display;
use quote::quote;
use quote::ToTokens;
use rustc_middle::ty::{Ty, TyCtxt};

#[derive(Debug, Clone)]
pub struct RefinementType<'tcx> {
    pub base: Ty<'tcx>,
    pub binder: String,
    pub predicate: syn::Expr,
}

impl<'a> Display for RefinementType<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let pred = &self.predicate;
        write!(
            f,
            "ty!{{ {} : {:?} | {} }}",
            self.binder,
            self.base,
            quote! { #pred }
        )
    }
}

impl<'a> RefinementType<'a> {
    pub fn from_type_alias<'b, 'tcx>(
        raw_type: &'a hir::Ty<'a>,
        tcx: &'b TyCtxt<'tcx>,
        base_ty: Ty<'a>,
    ) -> anyhow::Result<RefinementType<'a>> {
        if let Some((_base, binder, raw_predicate)) = raw_type.try_into_refinement(tcx) {
            let predicate = parse_predicate(raw_predicate.as_str())?;
            Ok(RefinementType {
                base: base_ty,
                binder: binder.as_str().to_string(),
                predicate,
            })
        } else {
            Err(anyhow!(
                "type {:?} does not seem to be a refinement type, when one was expected",
                raw_type
            ))
        }
    }

    pub fn encode_smt(&self, name: &str) -> String {
        let body = encode_smt(&self.predicate);
        let args = format!("({} Int)", self.binder);
        format!("(define-fun {} ({}) Bool ({})", name, args, body)
    }
}

pub fn encode_smt(expr: &syn::Expr) -> String {
    match expr {
        syn::Expr::Binary(syn::ExprBinary {
            left, right, op, ..
        }) => {
            let smt_op = match op {
                syn::BinOp::Add(_) => "+",
                syn::BinOp::Sub(_) => "-",
                syn::BinOp::Mul(_) => "*",
                syn::BinOp::Div(_) => "/",
                syn::BinOp::And(_) => "&&",
                syn::BinOp::Or(_) => "||",
                syn::BinOp::Eq(_) => "=",
                syn::BinOp::Lt(_) => "<",
                syn::BinOp::Le(_) => "<=",
                syn::BinOp::Ge(_) => ">=",
                syn::BinOp::Gt(_) => ">",
                _ => todo!(),
            };
            format!("({} {} {})", smt_op, encode_smt(left), encode_smt(right))
        }
        syn::Expr::Lit(syn::ExprLit { lit, .. }) => match lit {
            syn::Lit::Str(_) => todo!(),
            syn::Lit::ByteStr(_) => todo!(),
            syn::Lit::Byte(_) => todo!(),
            syn::Lit::Char(_) => todo!(),
            syn::Lit::Int(lit) => lit.to_token_stream().to_string(),
            syn::Lit::Float(_) => todo!(),
            syn::Lit::Bool(_) => todo!(),
            syn::Lit::Verbatim(_) => todo!(),
        },
        syn::Expr::Path(syn::ExprPath {
            path: syn::Path { segments, .. },
            ..
        }) => match segments.first() {
            Some(syn::PathSegment { ident, .. }) => format!("{}", ident),
            _ => todo!(),
        },
        _other => todo!("expr: {:?}", expr),
    }
}

fn parse_predicate(raw_predicate: &str) -> anyhow::Result<syn::Expr> {
    let parsed = syn::parse_str::<syn::Expr>(raw_predicate)?;
    Ok(parsed)
}
