use crate::refinements;
use anyhow::anyhow;
use quote::quote;
use rsmt2::SmtConf;
use rsmt2::Solver;
use rustc_ast as ast;
use rustc_ast_pretty::pprust;
use rustc_hir as hir;
use rustc_hir::Ty;
use rustc_hir::{Expr, ExprKind};
use rustc_middle::ty::TypeckResults;
use rustc_middle::ty::{query::TyCtxtAt, TyCtxt};
use rustc_span::source_map::Spanned;
use tracing::error;
use std::io::Write;
use syn::__private::ToTokens;
use syn::parse_quote;
use tracing::info;

use crate::hir_ext::ExprExt;
use crate::refinements::{extract_refinement_from_type_alias, RefinementType};

macro_rules! sexp {
    ($assert:tt) => {{
        stringify! {$assert}.to_string()
    }};
}

pub type RContext<'a> = Vec<CtxEntry<'a>>;

fn encode_refinement_context<'a>(ctx: RContext<'a>) -> String {
    ctx.iter()
        .map(|entry| entry.encode_smt())
        .collect::<Vec<_>>()
        .join("\n")
}

pub enum CtxEntry<'a> {
    Typed {
        ident: String,
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
            CtxEntry::Typed { ident, ty } => format!("XXX"),
        }
    }
}

pub fn type_of<'a, 'tcx, P>(
    expr: &'a Expr<'tcx>,
    tcx: &'a TyCtxt<'tcx>,
    ctx: &'a RContext<'a>,
    local_ctx: &'a TypeckResults<'a>,
    solver: &mut Solver<P>,
) -> anyhow::Result<RefinementType<'a>>
where
    // 'tcx at least as long as 'a
    'tcx: 'a,
{
    match &expr.kind {
        ExprKind::Lit(Spanned { node, span }) => {
            let lit: syn::Expr = syn::parse_str(&expr.pretty_print())?;
            let predicate = parse_quote! {
                v == #lit
            };
            info!(pred=?predicate, "Expr Literal gets predicate");
            let base = local_ctx.node_type(expr.hir_id);

            anyhow::Ok(RefinementType {
                base,
                binder: "v".to_string(),
                predicate,
            })
        }
        ExprKind::Block(hir::Block { stmts, expr, .. }, None) => {
            assert_eq!(stmts.len(), 0, "unexpected stmts {:?}", stmts);
            match expr {
                Some(expr) => type_of(expr, tcx, ctx, local_ctx, solver),
                None => todo!("dont know how to handle block without expr (yet)"),
            }
        }
        ExprKind::Block(_, Some(_)) => {
            todo!("labels are not yet supported")
        }
        ExprKind::Path(_) => todo!(),
        ExprKind::Box(_) => todo!(),
        ExprKind::ConstBlock(_) => todo!(),
        ExprKind::Array(_) => todo!(),
        ExprKind::Call(_, _) => todo!(),
        ExprKind::MethodCall(_, _, _) => todo!(),
        ExprKind::Tup(contents) => {
            let tuple_type = local_ctx.expr_ty(expr);
            info!(?tuple_type);
            let ty = match contents {
                [] => RefinementType {
                    base: tuple_type,
                    binder: "v".to_string(),
                    predicate: parse_quote! { true },
                },
                o => todo!(),
            };
            anyhow::Ok(ty)
        }
        ExprKind::Binary(_, _, _) => todo!(),
        ExprKind::Unary(_, _) => todo!(),
        ExprKind::Cast(expr, cast_ty) => {
            // Generate sub-typing constraint
            let expr_ty = type_of(expr, tcx, ctx, local_ctx, solver)?;

            let cast_refinement = extract_refinement_from_type_alias(cast_ty, tcx, local_ctx)?;
            let super_ty = RefinementType {
                base: local_ctx.expr_ty(&expr),
                binder: cast_refinement.0,
                predicate: cast_refinement.1,
            };

            // SMT Subtyping
            {
                info!(
                    "need to do subtyping judgement: {} >= {}",
                    super_ty, expr_ty
                );
                solver.push(1).unwrap();
                solver.define_fun(
                    "super_ty",
                    &[(&super_ty.binder, "Int")],
                    "Bool",
                    refinements::encode_smt(&super_ty.predicate),
                );
                solver.define_fun(
                    "sub_ty",
                    &[(&expr_ty.binder, "Int")],
                    "Bool",
                    refinements::encode_smt(&expr_ty.predicate),
                );
                solver.declare_const("inst", "Int");
                solver.assert("(not (=> (sub_ty inst) (super_ty inst)))");
                let is_sat = solver.check_sat().unwrap();
                solver.pop(1);
                if is_sat {
                    let msg = format!("Subtyping judgement failed: {} is not a subtype of {}", &expr_ty, &super_ty);
                    error!("{}", msg);
                    Err(anyhow!(msg))?;
                } else {
                    info!("no counterexample found 🮱")
                    // no counterexample found => everything is fine => continue
                }
            }

            anyhow::Ok(super_ty)
        }
        ExprKind::Type(_, _) => todo!(),
        ExprKind::DropTemps(_) => todo!(),
        ExprKind::If(_, _, _) => todo!(),
        ExprKind::Loop(_, _, _, _) => todo!(),
        ExprKind::Match(_, _, _) => todo!(),
        ExprKind::Closure(_, _, _, _, _) => todo!(),
        ExprKind::Assign(_, _, _) => todo!(),
        ExprKind::AssignOp(_, _, _) => todo!(),
        ExprKind::Field(_, _) => todo!(),
        ExprKind::Index(_, _) => todo!(),
        ExprKind::AddrOf(_, _, _) => todo!(),
        ExprKind::Break(_, _) => todo!(),
        ExprKind::Continue(_) => todo!(),
        ExprKind::Ret(_) => todo!(),
        ExprKind::InlineAsm(_) => todo!(),
        ExprKind::Struct(_, _, _) => todo!(),
        ExprKind::Repeat(_, _) => todo!(),
        ExprKind::Yield(_, _) => todo!(),
        ExprKind::Err => todo!(),
        e => todo!("expr: {:?}", e),
    }
}

pub fn type_of_node<'a, 'tcx>(
    node: &'a hir::Node<'tcx>,
    tcx: &'a TyCtxt<'tcx>,
    local_ctx: &'a TypeckResults<'a>,
    ctx: &'a RContext<'a>,
) -> anyhow::Result<RefinementType<'a>>
where
    'tcx: 'a,
{
    let parser = ();
    let conf = SmtConf::default_z3();
    let mut solver = conf.spawn(parser).unwrap();

    match node {
        hir::Node::Expr(expr) => type_of(expr, tcx, ctx, local_ctx, &mut solver),
        o => todo!(),
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::test_with_rustc::with_expr;
    use pretty_assertions as pretty;
    use rsmt2::SmtConf;
    use tracing::{error, trace};

    #[test_log::test]
    fn test_smt() {
        let parser = ();

        let conf = SmtConf::default_z3();
        let mut solver = conf.spawn(parser).unwrap();
        solver.declare_const("a", "Int").unwrap();

        let ass = sexp! {
          (> a 2)
        };
        dbg!(ass.clone());
        solver.assert(ass);

        let is_sat = solver.check_sat().unwrap();
        assert!(is_sat);
        let model = solver.get_model().unwrap();
        println!("{:?}", model);
    }

    #[test_log::test]
    fn test_type_of_lit() {
        with_expr(
            &quote! {
                // type Refinement<T, const B: &'static str, const R: &'static str> = T;
                fn f() ->i32{ 1 }
            }
            .to_string(),
            |expr, tcx, local_ctx| {
                let conf = SmtConf::default_z3();
                let mut solver = conf.spawn(()).unwrap();
                
                let ctx = vec![];
                let ty = type_of(expr, &tcx, &ctx, local_ctx, &mut solver).unwrap();
                pretty::assert_eq!(ty.to_string(), "ty!{ v : i32 | v == 1 }");
                info!("{}", ty);
            },
        )
        .unwrap();
    }

    #[test_log::test]
    fn test_subtype_lit_pos() {
        with_expr(
            &quote! {
                type Refinement<T, const B: &'static str, const R: &'static str> = T;

                fn f() ->i32{ 1 as Refinement<i32, "x", "x > 0"> }
            }
            .to_string(),
            |expr, tcx, local_ctx| {
                let conf = SmtConf::default_z3();
                let mut solver = conf.spawn(()).unwrap();
                solver.path_tee("/tmp/z3");
                let ctx = vec![];
                let ty = type_of(expr, &tcx, &ctx, local_ctx, &mut solver).unwrap();
                pretty::assert_eq!(ty.to_string(), "ty!{ x : i32 | x > 0 }");
                info!("expr has type {}", ty);
            },
        )
        .unwrap();
    }

    #[should_panic]
    #[test_log::test]
    fn test_subtype_lit_neg() {
        with_expr(
            &quote! {
                type Refinement<T, const B: &'static str, const R: &'static str> = T;

                fn f() -> i32 { 1 as Refinement<i32, "x", "x < 0"> }
            }
            .to_string(),
            |expr, tcx, local_ctx| {
                let conf = SmtConf::default_z3();
                let mut solver = conf.spawn(()).unwrap();
                solver.path_tee("/tmp/z3");
                let ctx = vec![];
                let ty = type_of(expr, &tcx, &ctx, local_ctx, &mut solver).unwrap(); // <- panic happens here
            },
        )
        .unwrap();
    }

    #[test_log::test]
    fn test_subtype_lit_pos_nested() {
        with_expr(
            &quote! {
                type Refinement<T, const B: &'static str, const R: &'static str> = T;

                fn f() ->i32{ (3 as Refinement<i32, "x", "x > 2">) as Refinement<i32, "x", "x > 1"> }
            }
            .to_string(),
            |expr, tcx, local_ctx| {
                let conf = SmtConf::default_z3();
                let mut solver = conf.spawn(()).unwrap();
                solver.path_tee("/tmp/z3");
                let ctx = vec![];
                let ty = type_of(expr, &tcx, &ctx, local_ctx, &mut solver).unwrap();
                pretty::assert_eq!(ty.to_string(), "ty!{ x : i32 | x > 1 }");
                info!("expr has type {}", ty);
            },
        )
        .unwrap();
    }
}
