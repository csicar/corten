use crate::hir_ext::TyExt;
use anyhow::anyhow;
use rustc_hir as hir;
use tracing::trace;

use core::fmt::Display;
use quote::quote;
use quote::ToTokens;
use rustc_middle::ty::{Ty, TyCtxt};

#[derive(Debug, Clone)]
pub enum RefinementType<'tcx> {
    Mut(MutRefType<'tcx>),
    Imm(ImmRefType<'tcx>),
}

#[derive(Debug, Clone)]
pub struct MutRefType<'tcx> {
    pub base: Ty<'tcx>,
    pub before: Refinement,
    pub after: Refinement,
}


/// Immutable refinement type
/// `ty!{ x: i32 | x > 0 }`
/// - `base` is `i32`
/// - `refinement` is `x, x > 0`
#[derive(Debug, Clone)]
pub struct ImmRefType<'tcx> {
    pub base: Ty<'tcx>,
    pub refinement: Refinement,
}

#[derive(Debug, Clone)]
pub struct Refinement {
    pub binder: String,
    pub predicate: syn::Expr,
}

impl<'tcx> RefinementType<'tcx> {
    fn base(&self) -> Ty<'tcx> {
        match self {
            RefinementType::Mut(m) => m.base,
            RefinementType::Imm(i) => i.base,
        }
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
            Ok(RefinementType::Imm(ImmRefType {
                base: base_ty,
                refinement: Refinement {
                    binder: binder.as_str().to_string(),
                    predicate,
                },
            }))
        } else {
            Err(anyhow!(
                "type {:?} does not seem to be a refinement type, when one was expected",
                raw_type
            ))
        }
    }
}

impl<'tcx> Into<RefinementType<'tcx>> for MutRefType<'tcx> {
    fn into(self) -> RefinementType<'tcx> {
        RefinementType::Mut(self)
    }
}

impl<'tcx> Display for MutRefType<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let pred_before = &self.before.predicate;
        let pred_after = &self.after.predicate;
        write!(
            f,
            "ty!{{ {} : {:?} | {} => {} | {} }}",
            self.before.binder,
            self.base,
            quote! { #pred_before },
            self.after.binder,
            quote! { #pred_after }
        )
    }
}

impl<'tcx> ImmRefType<'tcx> {
    pub fn rename_binder(&self, new_name: &str) -> anyhow::Result<ImmRefType<'tcx>> {
        Ok(ImmRefType {
            base: self.base,
            refinement: Refinement {
                binder: new_name.to_string(),
                predicate: rename_ref_in_expr(
                    &self.refinement.predicate,
                    &self.refinement.binder,
                    new_name,
                )?,
            },
        })
    }

    pub fn encode_smt(&self, name: &str) -> String {
        let body = encode_smt(&self.refinement.predicate);
        let args = format!("({} Int)", self.refinement.binder);
        format!("(define-fun {} ({}) Bool ({})", name, args, body)
    }
}

impl<'tcx> Into<RefinementType<'tcx>> for ImmRefType<'tcx> {
    fn into(self) -> RefinementType<'tcx> {
        RefinementType::Imm(self)
    }
}

impl<'tcx> Display for ImmRefType<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let pred = &self.refinement.predicate;
        write!(
            f,
            "ty!{{ {} : {:?} | {} }}",
            self.refinement.binder,
            self.base,
            quote! { #pred }
        )
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
                    if local_var.ident.to_string() == old_name {
                        let new_ident = syn::Ident::new(new_name, local_var.ident.span());
                        new_path.path.segments.first_mut().unwrap().ident = new_ident;
                        Ok(syn::Expr::Path(new_path))
                    } else {
                        Ok(expr.clone())
                    }
                }
                _other => todo!(),
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
        match self {
            RefinementType::Mut(m) => m.fmt(f),
            RefinementType::Imm(i) => i.fmt(f),
        }
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
        syn::Expr::Unary(syn::ExprUnary { op, expr, .. }) => {
            let smt_op = match op {
                syn::UnOp::Deref(_) => todo!(),
                syn::UnOp::Not(_) => "not",
                syn::UnOp::Neg(_) => "-",
            };
            format!("({} {})", smt_op, encode_smt(expr))
        }
        syn::Expr::Lit(syn::ExprLit { lit, .. }) => match lit {
            syn::Lit::Str(str) => todo!("{:?}", str),
            syn::Lit::ByteStr(_) => todo!(),
            syn::Lit::Byte(_) => todo!(),
            syn::Lit::Char(_) => todo!(),
            syn::Lit::Int(lit) => lit.to_token_stream().to_string(),
            syn::Lit::Float(_) => todo!(),
            syn::Lit::Bool(_bool) => lit.to_token_stream().to_string(),
            syn::Lit::Verbatim(_) => todo!(),
        },
        syn::Expr::Path(syn::ExprPath {
            path: syn::Path { segments, .. },
            ..
        }) => match segments.first() {
            Some(syn::PathSegment { ident, .. }) => encode_ident(ident),
            _ => todo!(),
        },
        syn::Expr::Paren(syn::ExprParen { expr, .. }) => {
            format!("{}", encode_smt(expr))
        }
        syn::Expr::Block(syn::ExprBlock {
            block: syn::Block { stmts, .. },
            label: None,
            ..
        }) => {
            // This occurs is necessary for typing some conditions like:
            // typing cond: cond={ let _t = a > 0; _t } then_expr={ a } else_expr={ 1 as Refinement<i32, , > }
            // Rust HIR decides to introduce a tmp var for the condition
            // => translate to `(let (_t (> a 0)) _t)`

            if let Some((syn::Stmt::Expr(in_expr), var_declarations)) = stmts.split_last() {
                let converted = var_declarations
                    .iter()
                    .map(|decl| encode_let_binding_smt(decl).unwrap())
                    .collect::<Vec<String>>();
                let block_enc = format!("(let ({}) {})", converted.join(" "), encode_smt(in_expr));
                trace!("encoding of block is {}", block_enc);
                block_enc
            } else {
                todo!()
            }
        }
        _other => todo!("expr: {:?}", expr),
    }
}

/// Given `let _t = a > 0;` returns `(_t (> a 0))`
/// ```
/// use syn;
/// let input = parse_quote! { let _t = a > 0; }
/// let output = encode_let_binding_smt(input);
/// assert_eq(output, "(_t (> a 0))");
/// ```
fn encode_let_binding_smt(decl: &syn::Stmt) -> anyhow::Result<String> {
    match decl {
        syn::Stmt::Local(syn::Local {
            pat:
                syn::Pat::Ident(syn::PatIdent {
                    attrs: _,
                    mutability: None,
                    by_ref: None,
                    subpat: None,
                    ident,
                }),
            init: Some((_, expr)),
            ..
        }) => {
            trace!(?ident, ?expr, "encode binding");

            Ok(format!("({} {})", encode_ident(ident), encode_smt(expr)))
        }
        other => todo!("unknown: {:?}", other),
    }
}

fn encode_ident(ident: &syn::Ident) -> String {
    format!("|{}|", ident)
}

fn parse_predicate(raw_predicate: &str) -> anyhow::Result<syn::Expr> {
    let parsed = syn::parse_str::<syn::Expr>(raw_predicate)?;
    Ok(parsed)
}
#[cfg(test)]
mod test {
    use pretty_assertions as pretty;
    use syn::parse_quote;

    use super::*;

    #[test_log::test]
    fn test_encode_let_binding() {
        let input: Vec<_> = parse_quote! { let _t = a > 0; };
        let output = encode_let_binding_smt(&input[0]).unwrap();
        pretty::assert_eq!(output, "(|_t| (> |a| 0))");
    }

    #[test_log::test]
    fn test_encode_expr_with_let() {
        let input = parse_quote! { { let _t = a > 0; _t } };
        let output = encode_smt(&input);
        pretty::assert_eq!(output, "(let ((|_t| (> |a| 0))) |_t|)");
    }
}
