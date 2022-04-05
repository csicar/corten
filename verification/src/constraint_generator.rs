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

pub enum CtxEntry<'a> {
    Typed {
        ident: String,
        ty: RefinementType<'a>,
    },
    Formula {
        expr: syn::Expr,
    },
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

            info!(
                "need to do subtyping judgement: {} >= {}",
                super_ty, expr_ty
            );

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
    use rsmt2::SmtConf;
    use tracing::{trace, error};

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
                #![feature(adt_const_params)]

                type Refinement<T, const B: &'static str, const R: &'static str> = T;
                
                fn f() ->i32{ 1 }
                // fn main() {}
            }
            .to_string(),
            |expr, tcx, local_ctx| {
                let conf = SmtConf::default_z3();
                let mut solver = conf.spawn(()).unwrap();
                let ctx = vec![];
                let ty = type_of(expr, &tcx, &ctx, local_ctx, &mut solver).unwrap();
                info!(?ty);
            },
        )
        .unwrap();
    }
}
