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

    pub fn rename_binder(&self, new_name: &str) -> anyhow::Result<RefinementType<'a>> {
        Ok(RefinementType {
            base: self.base,
            binder: new_name.to_string(),
            predicate: rename_ref_in_expr(&self.predicate, &self.binder, new_name)?,
        })
    }

    pub fn encode_smt(&self, name: &str) -> String {
        let body = encode_smt(&self.predicate);
        let args = format!("({} Int)", self.binder);
        format!("(define-fun {} ({}) Bool ({})", name, args, body)
    }
}

fn rename_ref_in_expr(
    expr: &syn::Expr,
    old_name: &str,
    new_name: &str,
) -> anyhow::Result<syn::Expr> {
    match expr {
        syn::Expr::Array(_) => todo!(),
        syn::Expr::Assign(_) => todo!(),
        syn::Expr::AssignOp(_) => todo!(),
        syn::Expr::Async(_) => todo!(),
        syn::Expr::Await(_) => todo!(),
        syn::Expr::Binary(syn::ExprBinary {
            attrs,
            left,
            op,
            right,
        }) => Ok(syn::Expr::Binary(syn::ExprBinary {
            attrs: attrs.clone(),
            left: Box::new(rename_ref_in_expr(left, old_name, new_name)?),
            op: op.clone(),
            right: Box::new(rename_ref_in_expr(right, old_name, new_name)?),
        })),
        syn::Expr::Block(_) => todo!(),
        syn::Expr::Box(_) => todo!(),
        syn::Expr::Break(_) => todo!(),
        syn::Expr::Call(_) => todo!(),
        syn::Expr::Cast(_) => todo!(),
        syn::Expr::Closure(_) => todo!(),
        syn::Expr::Continue(_) => todo!(),
        syn::Expr::Field(_) => todo!(),
        syn::Expr::ForLoop(_) => todo!(),
        syn::Expr::Group(_) => todo!(),
        syn::Expr::If(_) => todo!(),
        syn::Expr::Index(_) => todo!(),
        syn::Expr::Let(_) => todo!(),
        syn::Expr::Lit(_) => Ok(expr.clone()),
        syn::Expr::Loop(_) => todo!(),
        syn::Expr::Macro(_) => todo!(),
        syn::Expr::Match(_) => todo!(),
        syn::Expr::MethodCall(_) => todo!(),
        syn::Expr::Paren(_) => todo!(),
        syn::Expr::Path(
            expr_path @ syn::ExprPath {
                path: syn::Path { segments, .. },
                ..
            },
        ) => {
            let path: Vec<&syn::PathSegment> = segments.iter().collect();
            let mut new_path = expr_path.clone();
            match &path[..] {
                [local_var] => {
                    if (local_var.ident.to_string() == old_name) {
                        let new_ident = syn::Ident::new(new_name, local_var.ident.span());
                        new_path.path.segments.first_mut().unwrap().ident = new_ident;
                        Ok(syn::Expr::Path(new_path))
                    } else {
                        Ok(expr.clone())
                    }
                }
                other => todo!(),
            }
        }
        syn::Expr::Range(_) => todo!(),
        syn::Expr::Reference(_) => todo!(),
        syn::Expr::Repeat(_) => todo!(),
        syn::Expr::Return(_) => todo!(),
        syn::Expr::Struct(_) => todo!(),
        syn::Expr::Try(_) => todo!(),
        syn::Expr::TryBlock(_) => todo!(),
        syn::Expr::Tuple(_) => todo!(),
        syn::Expr::Type(_) => todo!(),
        syn::Expr::Unary(_) => todo!(),
        syn::Expr::Unsafe(_) => todo!(),
        syn::Expr::Verbatim(_) => todo!(),
        syn::Expr::While(_) => todo!(),
        syn::Expr::Yield(_) => todo!(),
        other => anyhow::bail!("don't know how rename expr node {:?} in a predicate", other),
    }
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
            syn::Lit::Str(str) => todo!("{:?}", str),
            syn::Lit::ByteStr(_) => todo!(),
            syn::Lit::Byte(_) => todo!(),
            syn::Lit::Char(_) => todo!(),
            syn::Lit::Int(lit) => lit.to_token_stream().to_string(),
            syn::Lit::Float(_) => todo!(),
            syn::Lit::Bool(bool) => lit.to_token_stream().to_string(),
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
