use crate::hir_ext::TyExt;
use crate::refinement_context::TypeTarget;
use anyhow::anyhow;
use anyhow::Context;
use rustc_hir as hir;
use rustc_middle::ty::TypeckResults;
use syn::parse_quote;
use syn::spanned::Spanned;
use syn::visit::Visit;
use syn::ExprCall;
use tracing::instrument;
use tracing::trace;

use core::fmt::Display;
use quote::quote;
use quote::ToTokens;
use rustc_middle::ty::{Ty, TyCtxt};
use std::collections::HashSet;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RefinementType<'tcx> {
    pub base: Ty<'tcx>,
    pub binder: String,
    pub predicate: syn::Expr,
}

impl<'a> RefinementType<'a> {
    /// Extracts the Refinement Type from a `Refinement<T, B, P>` type alias
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

    pub fn new_empty_refinement_for(
        expr: &hir::Expr,
        local_ctx: &TypeckResults<'a>,
        fresh_binder: String,
    ) -> RefinementType<'a> {
        let unit_type = local_ctx.expr_ty(expr);
        RefinementType {
            base: unit_type,
            binder: fresh_binder,
            predicate: parse_quote! { true },
        }
    }

    pub fn get_reference_type_in_expr(expr: &syn::Expr) -> anyhow::Result<TypeTarget<syn::Ident>> {
        match expr {
            // matches <sth> = &arg(<literal>)
            syn::Expr::Binary(syn::ExprBinary {
                left: _,
                op: syn::BinOp::Eq(_),
                right:
                    box syn::Expr::Reference(syn::ExprReference {
                        mutability: _,
                        expr:
                            box syn::Expr::Call(syn::ExprCall {
                                func: box syn::Expr::Path(syn::ExprPath { path: fn_name, .. }),
                                args,
                                ..
                            }),
                        ..
                    }),
                ..
            }) => {
                if fn_name.get_ident().unwrap() == "arg" && args.len() == 1 {
                    let arg = args.first().unwrap();
                    match arg {
                        syn::Expr::Lit(syn::ExprLit {
                            lit: syn::Lit::Int(v),
                            ..
                        }) => Ok(TypeTarget::Anonymous(v.base10_parse()?)),
                        _ => todo!("{}", quote! {#arg}),
                    }
                } else {
                    Err(anyhow!("unexpected fn call"))
                }
            }
            syn::Expr::Binary(syn::ExprBinary {
                left: _,
                op: syn::BinOp::Eq(_),
                right:
                    box syn::Expr::Reference(syn::ExprReference {
                        mutability: _,
                        expr: inner,
                        ..
                    }),
                ..
            }) => match inner {
                box syn::Expr::Path(syn::ExprPath { path, .. }) => {
                    Ok(TypeTarget::Definition(path.get_ident().cloned().unwrap()))
                }
                _ => todo!(),
            },

            _ => Err(anyhow!(
                "dont know how to create reference type from {}",
                quote! {#expr}
            )),
        }
    }

    /// Tries to get the type contents as a reference type:
    /// E.g. `ty!{ v: &mut i32 | v == &a }` => a
    pub fn get_as_reference_type(&self) -> anyhow::Result<TypeTarget<syn::Ident>> {
        RefinementType::get_reference_type_in_expr(&self.predicate)
            .with_context(|| format!("on refinement type {self}"))
    }

    pub fn rename_binder(&self, new_name: &str) -> anyhow::Result<RefinementType<'a>> {
        self.rename_binders(&|name| {
            if name == self.binder {
                new_name.to_string()
            } else {
                name.to_string()
            }
        })
    }

    /// Create a new RefinementType where predicate is the conjunction of self's predicate and
    /// [additional_predicate]
    pub fn with_additional_predicate(&self, additional_predicate: syn::Expr) -> RefinementType<'a> {
        RefinementType {
            predicate: syn::Expr::Binary(syn::ExprBinary {
                attrs: Vec::new(),
                left: Box::new(self.predicate.clone()),
                op: syn::BinOp::And(syn::Token![&&](additional_predicate.span())),
                right: Box::new(additional_predicate),
            }),
            ..self.clone()
        }
    }

    pub fn rename_binders(
        &self,
        renamer: &impl Fn(&str) -> String,
    ) -> anyhow::Result<RefinementType<'a>> {
        Ok(RefinementType {
            base: self.base,
            binder: renamer(&self.binder),
            predicate: rename_ref_in_expr(&self.predicate, renamer)?,
        })
    }

    pub fn free_vars(&self) -> HashSet<String> {
        let mut free_vars = vars_in_expr(&self.predicate);
        free_vars.remove(&self.binder);
        free_vars
    }
}

struct FreeVarsVisitor {
    free_vars: HashSet<String>,
}

impl<'ast> syn::visit::Visit<'ast> for FreeVarsVisitor {
    fn visit_path(&mut self, node: &'ast syn::Path) {
        let path: Vec<&syn::PathSegment> = node.segments.iter().collect();
        match &path[..] {
            [local_var] => {
                self.free_vars.insert(local_var.ident.to_string());
            }
            _other => todo!(),
        }
    }
}

pub fn vars_in_expr(expr: &syn::Expr) -> HashSet<String> {
    let mut visitor = FreeVarsVisitor {
        free_vars: HashSet::new(),
    };
    visitor.visit_expr(expr);
    visitor.free_vars
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MutRefinementType<'tcx> {
    pub start: RefinementType<'tcx>,
    pub end: RefinementType<'tcx>,
}

impl<'tcx> MutRefinementType<'tcx> {
    pub fn from_type_alias(
        raw_type: &hir::Ty<'tcx>,
        tcx: &TyCtxt<'tcx>,
        base_ty: Ty<'tcx>,
    ) -> anyhow::Result<MutRefinementType<'tcx>> {
        if let Some((_base, binder1, raw_predicate1, binder2, raw_predicate2)) =
            raw_type.try_into_mut_refinement(tcx)
        {
            let predicate1 = parse_predicate(raw_predicate1.as_str())?;
            let predicate2 = parse_predicate(raw_predicate2.as_str())?;
            Ok(MutRefinementType {
                start: RefinementType {
                    base: base_ty,
                    binder: binder1.as_str().to_string(),
                    predicate: predicate1,
                },
                end: RefinementType {
                    base: base_ty,
                    binder: binder2.as_str().to_string(),
                    predicate: predicate2,
                },
            })
        } else {
            Err(anyhow!(
                "type {:?} does not seem to be a mutable refinement type, when one was expected",
                raw_type
            ))
        }
    }

    pub fn rename_binders(
        &self,
        renamer: &impl Fn(&str) -> String,
    ) -> anyhow::Result<MutRefinementType<'tcx>> {
        Ok(MutRefinementType {
           start: self.start.rename_binders(renamer)?,
           end: self.end.rename_binders(renamer)?
        })
    }

}

pub fn rename_ref_in_expr(
    expr: &syn::Expr,
    renamer: &impl Fn(&str) -> String,
) -> anyhow::Result<syn::Expr> {
    match expr {
        syn::Expr::Array(_) => todo!(),
        syn::Expr::Assign(_) => {
            anyhow::bail!("`=` is not allowed in refinement type. Did you mean `==`?")
        }
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
            left: Box::new(rename_ref_in_expr(left, renamer)?),
            op: op.clone(),
            right: Box::new(rename_ref_in_expr(right, renamer)?),
        })),
        syn::Expr::Block(_) => todo!(),
        syn::Expr::Box(_) => todo!(),
        syn::Expr::Break(_) => todo!(),
        syn::Expr::Call(ExprCall {
            attrs,
            func,
            paren_token,
            args,
        }) => {
            let renamed_args = args
                .iter()
                .map(|arg| rename_ref_in_expr(arg, renamer))
                .collect::<anyhow::Result<_>>()?;

            Ok(syn::Expr::Call(ExprCall {
                attrs: attrs.clone(),
                func: func.clone(),
                paren_token: paren_token.clone(),
                args: renamed_args,
            }))
        }
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
        syn::Expr::Paren(syn::ExprParen {
            attrs,
            paren_token,
            expr: inner_expr,
        }) => Ok(syn::Expr::Paren(syn::ExprParen {
            expr: Box::new(rename_ref_in_expr(inner_expr, renamer)?),
            attrs: attrs.clone(),
            paren_token: paren_token.clone(),
        })),
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
                    let new_name = renamer(&local_var.ident.to_string());
                    let new_ident = syn::Ident::new(&new_name, local_var.ident.span());
                    new_path.path.segments.first_mut().unwrap().ident = new_ident;
                    Ok(syn::Expr::Path(new_path))
                }
                _other => todo!(),
            }
        }
        syn::Expr::Range(_) => todo!(),
        syn::Expr::Reference(syn::ExprReference {
            attrs,
            and_token,
            raw,
            mutability,
            expr: inner,
        }) => anyhow::Ok(syn::Expr::Reference(syn::ExprReference {
            attrs: attrs.clone(),
            and_token: and_token.clone(),
            raw: raw.clone(),
            mutability: mutability.clone(),
            expr: Box::new(rename_ref_in_expr(inner, renamer)?),
        })),
        syn::Expr::Repeat(_) => todo!(),
        syn::Expr::Return(_) => todo!(),
        syn::Expr::Struct(_) => todo!(),
        syn::Expr::Try(_) => todo!(),
        syn::Expr::TryBlock(_) => todo!(),
        syn::Expr::Tuple(_) => todo!(),
        syn::Expr::Type(_) => todo!(),
        syn::Expr::Unary(syn::ExprUnary {
            attrs,
            op,
            expr: inner,
        }) => anyhow::Ok(syn::Expr::Unary(syn::ExprUnary {
            attrs: attrs.clone(),
            op: op.clone(),
            expr: Box::new(rename_ref_in_expr(inner, renamer)?),
        })),
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

/// Arguments:
/// - expr to encode
/// - For `arg(0)` or `pvar` we will need to find their logic binder.
pub fn encode_smt(
    expr: &syn::Expr,
    target_to_binder: &impl Fn(&TypeTarget<syn::Ident>) -> String,
) -> String {
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
                syn::BinOp::Or(_) => "or",
                syn::BinOp::Eq(_) => "=",
                syn::BinOp::Lt(_) => "<",
                syn::BinOp::Le(_) => "<=",
                syn::BinOp::Ge(_) => ">=",
                syn::BinOp::Gt(_) => ">",
                syn::BinOp::Rem(_) => "mod",
                _ => todo!("not implemented {op:?}"),
            };
            format!(
                "({} {} {})",
                smt_op,
                encode_smt(left, target_to_binder),
                encode_smt(right, target_to_binder)
            )
        }
        syn::Expr::Unary(syn::ExprUnary { op, expr, .. }) => {
            let inner_enc = encode_smt(expr, target_to_binder);
            match op {
                syn::UnOp::Deref(_) => inner_enc,
                syn::UnOp::Not(_) => format!("(not {})", inner_enc),
                syn::UnOp::Neg(_) => format!("(- {})", inner_enc),
            }
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
        syn::Expr::Paren(syn::ExprParen { expr, .. }) => encode_smt(expr, target_to_binder),
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
                    .map(|decl| encode_let_binding_smt(decl, target_to_binder).unwrap())
                    .collect::<Vec<String>>();
                let block_enc = format!(
                    "(let ({}) {})",
                    converted.join(" "),
                    encode_smt(in_expr, target_to_binder)
                );
                trace!("encoding of block is {}", block_enc);
                block_enc
            } else {
                todo!()
            }
        }
        syn::Expr::Reference(syn::ExprReference { expr: inner, .. }) => match inner {
            box syn::Expr::Path(syn::ExprPath { path, .. }) => {
                let ident = path.get_ident().unwrap();
                target_to_binder(&TypeTarget::Definition(ident.clone()))
            }
            box syn::Expr::Call(syn::ExprCall {
                func: box syn::Expr::Path(syn::ExprPath { path: fn_name, .. }),
                args,
                ..
            }) => {
                if fn_name.get_ident().unwrap() == "arg" && args.len() == 1 {
                    let arg = args.first().unwrap();
                    let arg_no = match arg {
                        syn::Expr::Lit(syn::ExprLit {
                            lit: syn::Lit::Int(v),
                            ..
                        }) => v.base10_parse::<usize>().unwrap(),
                        _ => todo!(),
                    };
                    target_to_binder(&TypeTarget::Anonymous(arg_no))
                } else {
                    todo!()
                }
            }
            _ => todo!("not implemented: {}", quote! {#expr}),
        },

        _other => todo!("expr: {}, {:?}", quote! { #expr }, expr),
    }
}

/// Given `let _t = a > 0;` returns `(_t (> a 0))`
/// ```
/// use syn;
/// let input = parse_quote! { let _t = a > 0; }
/// let output = encode_let_binding_smt(input);
/// assert_eq(output, "(_t (> a 0))");
/// ```
fn encode_let_binding_smt(
    decl: &syn::Stmt,
    target_to_binder: &impl Fn(&TypeTarget<syn::Ident>) -> String,
) -> anyhow::Result<String> {
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

            Ok(format!(
                "({} {})",
                encode_ident(ident),
                encode_smt(expr, target_to_binder)
            ))
        }
        other => todo!("unknown: {:?}", other),
    }
}

fn encode_ident(ident: &syn::Ident) -> String {
    format!("|{}|", ident)
}

pub fn parse_predicate(raw_predicate: &str) -> anyhow::Result<syn::Expr> {
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
        let output = encode_let_binding_smt(&input[0], &|_| todo!()).unwrap();
        pretty::assert_eq!(output, "(|_t| (> |a| 0))");
    }

    #[test_log::test]
    fn test_encode_expr_with_let() {
        let input = parse_quote! { { let _t = a > 0; _t } };
        let output = encode_smt(&input, &|_| todo!());
        pretty::assert_eq!(output, "(let ((|_t| (> |a| 0))) |_t|)");
    }
}
