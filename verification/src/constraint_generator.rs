

use crate::refinement_context::CtxEntry;
use crate::refinement_context::RContext;
use crate::refinements;
use crate::smtlib_ext::SmtResExt;
use anyhow::anyhow;

use quote::format_ident;
use rsmt2::SmtConf;
use rsmt2::Solver;
use rustc_hir as hir;

use rustc_hir::{Expr, ExprKind};
use rustc_middle::ty::TyCtxt;
use rustc_middle::ty::TypeckResults;
use rustc_span::source_map::Spanned;
use tracing::error;

use syn::parse_quote;
use tracing::info;
use tracing::trace;

use crate::hir_ext::ExprExt;
use crate::refinements::RefinementType;

pub fn type_check_function<'a, 'tcx, 'r>(
    function: &'a hir::Item<'tcx>,
    tcx: &'a TyCtxt<'tcx>,
) -> anyhow::Result<RefinementType<'r>>
where
    'a: 'r,
    'tcx: 'r,
{
    match function {
        hir::Item {
            kind:
                hir::ItemKind::Fn(
                    hir::FnSig {
                        decl: hir::FnDecl { output, inputs, .. },
                        ..
                    },
                    _,
                    body_id,
                ),
            ident: _,
            def_id,
            ..
        } => {
            trace!(node_to_string=?tcx.hir().node_to_string(function.hir_id()), "just for fun: print");
            let body = tcx.hir().body(body_id.clone());
            trace!(?body_id, ?body, "function body");
            trace!(?function, "full function");
            let local_ctx = tcx.typeck(*def_id);

            // Get middle::ty of function
            let sigs = local_ctx.liberated_fn_sigs();
            let fn_sig = sigs
                .get(function.hir_id())
                .ok_or(anyhow!("function not found in typeck result"))?;
            trace!(?fn_sig);

            // get refinements for inputs
            let mut ctx = RContext::new();
            for ((hir_ty, middle_ty), param) in inputs.iter().zip(fn_sig.inputs()).zip(body.params)
            {
                let refinement = RefinementType::from_type_alias(hir_ty, &tcx, middle_ty.clone())?;

                trace!(%refinement, %param.pat.hir_id, "input type");
                let res = CtxEntry::Typed {
                    ident: param.pat.hir_id,
                    ty: refinement,
                };
                ctx.add_entry(res)
            }
            // let ctx = Rc::new(ctx);

            // get refinement for output
            let expected_type = match output {
                hir::FnRetTy::Return(return_type) => {
                    RefinementType::from_type_alias(return_type, &tcx, fn_sig.output())
                }
                _ => todo!(),
            }?;
            trace!(%expected_type, "expected function type ");

            let conf = SmtConf::default_z3();
            let mut solver = conf.spawn(()).unwrap();
            solver.path_tee("/tmp/z3-fn.lisp").unwrap();

            let actual_ty = type_of(&body.value, &tcx, &ctx, local_ctx, &mut solver)?;
            trace!(%actual_ty, "actual function type");
            require_is_subtype_of(&actual_ty, &expected_type, &ctx, &mut solver)?;
            anyhow::Ok(expected_type)
        }
        other => Err(anyhow!(
            "tried to type check a function, but got a {:?} instead",
            other
        )),
    }
}

pub fn type_of<'a, 'b, 'c, 'tcx, P>(
    expr: &'a Expr<'tcx>,
    tcx: &'b TyCtxt<'tcx>,
    ctx: &'c RContext<'tcx>,
    local_ctx: &'a TypeckResults<'a>,
    solver: &mut Solver<P>,
) -> anyhow::Result<RefinementType<'a>>
where
    // 'tcx at least as long as 'a
    'tcx: 'a,
{
    match &expr.kind {
        ExprKind::Lit(Spanned { node: _, span: _ }) => {
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
        ExprKind::Path(path) => {
            // this is a variable reference
            // for
            // ```rust
            //  fn f(a: ty!{av : i32 | av > 0}) -> {
            //     a
            //  }
            // ```
            // Generates constraint `v: i32 | v > 0 && av == v`
            //
            let res = local_ctx.qpath_res(path, expr.hir_id);
            match res {
                hir::def::Res::Local(hir_id) => {
                    let ty_in_context = ctx.lookup_hir(&hir_id).ok_or(anyhow!(
                        "could not find refinement type definition of {:?} in refinement context",
                        hir_id
                    ))?;
                    let var_ty = ty_in_context.rename_binder("v_new_todo")?;
                    let combined_predicate = {
                        let new_pred = &var_ty.predicate;
                        let new_name = format_ident!("{}", &var_ty.binder);
                        let old_name = format_ident!("{}", &ty_in_context.binder);
                        parse_quote! {
                            #new_pred && #new_name == #old_name
                        }
                    };
                    let var_ty_with_eq_constraint = RefinementType { predicate: 
                        combined_predicate
                        , ..var_ty};
                    Ok(var_ty_with_eq_constraint)
                }
                hir::def::Res::Def(_, _) => todo!(),
                other => anyhow::bail!("reference to unexpected resolution {:?}", other),
            }
            // match path {
            //     hir::QPath::Resolved(None, hir::Path { res, .. }) => match res {
            //         hir::def::Res::Local(hir_id) => ctx.lookup_hir(hir_id).ok_or(anyhow!(
            //             "could not find refinement type definition of {:?} in refinement context",
            //             hir_id
            //         )),
            //         hir::def::Res::Def(_, _) => todo!(),
            //         other => anyhow::bail!("reference to unexpected resolution {:?}", other),
            //     },
            //     other => todo!(),
            // }
        }
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
                _o => todo!(),
            };
            anyhow::Ok(ty)
        }
        ExprKind::Binary(_, _, _) => todo!(),
        ExprKind::Unary(_, _) => todo!(),
        ExprKind::Cast(expr, cast_ty) => {
            // Generate sub-typing constraint
            let expr_ty = type_of(expr, tcx, ctx, local_ctx, solver)?;

            let super_ty = RefinementType::from_type_alias(cast_ty, tcx, local_ctx.expr_ty(&expr))?;

            // SMT Subtyping
            require_is_subtype_of(&expr_ty, &super_ty, ctx, solver)?;

            anyhow::Ok(super_ty)
        }
        ExprKind::Type(_, _) => todo!(),
        ExprKind::DropTemps(_) => todo!(),
        ExprKind::If(cond, then_expr, maybe_else_expr) => match maybe_else_expr {
            Some(_else_expr) => {
                let mut inner_ctx = ctx.clone();
                let cond_syn = syn::parse_str(&cond.pretty_print())?;
                inner_ctx.add_entry(CtxEntry::Formula { expr: cond_syn });
                let then_ty = type_of(then_expr, tcx, &inner_ctx, local_ctx, solver)?;
                anyhow::Ok(then_ty)
            }
            None => todo!(),
        },
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

fn require_is_subtype_of<'tcx, P>(
    sub_ty: &RefinementType<'tcx>,
    super_ty: &RefinementType<'tcx>,
    ctx: &RContext<'tcx>,
    solver: &mut Solver<P>,
) -> anyhow::Result<()> {
    info!("need to do subtyping judgement: {} ≼ {}", sub_ty, super_ty);
    solver.push(1).into_anyhow()?;
    ctx.encode_smt(solver)?;

    solver.declare_const(&sub_ty.binder, "Int").into_anyhow()?;
    solver.assert(refinements::encode_smt(&sub_ty.predicate)).into_anyhow()?;

    solver.declare_const(&super_ty.binder, "Int").into_anyhow()?;

    solver.assert(format!("(= {} {})", &super_ty.binder, &sub_ty.binder)).into_anyhow()?;

    solver.assert(format!("(not {})", refinements::encode_smt(&super_ty.predicate))).into_anyhow()?;

    // solver
    //     .define_fun(
    //         "super_ty",
    //         &[(&super_ty.binder, "Int")],
    //         "Bool",
    //         refinements::encode_smt(&super_ty.predicate),
    //     )
    //     .into_anyhow()?;
    // solver
    //     .define_fun(
    //         "sub_ty",
    //         &[(&sub_ty.binder, "Int")],
    //         "Bool",
    //         refinements::encode_smt(&sub_ty.predicate),
    //     )
    //     .into_anyhow()?;

    let is_sat = solver.check_sat().into_anyhow()?;
    solver.pop(2).into_anyhow()?;
    if is_sat {
        let msg = format!(
            "Subtyping judgement failed: {} is not a sub_ty of {}",
            &sub_ty, &super_ty
        );
        error!("{}", msg);
        Err(anyhow!(msg))?;
    } else {
        info!("no counterexample found 🮱")
        // no counterexample found => everything is fine => continue
    };
    Ok(())
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::test_with_rustc::{with_expr, with_item};
    use pretty_assertions as pretty;
    use quote::quote;
    use rsmt2::SmtConf;
    

    #[test_log::test]
    fn test_smt() {
        let parser = ();

        let conf = SmtConf::default_z3();
        let mut solver = conf.spawn(parser).unwrap();
        solver.declare_const("a", "Int").unwrap();

        let ass = "(> a 2)".to_string();
        dbg!(ass.clone());
        solver.assert(ass).unwrap();

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

                let ctx = RContext::new();
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
                solver.path_tee("/tmp/z3").unwrap();
                let ctx = RContext::new();
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
                solver.path_tee("/tmp/z3").unwrap();
                let ctx = RContext::new();
                let _ty = type_of(expr, &tcx, &ctx, local_ctx, &mut solver).unwrap();
                // <- panic happens here
            },
        )
        .unwrap();
    }

    #[test_log::test]
    fn test_subtype_lit_pos_nested() {
        with_expr(
            &quote! {
                type Refinement<T, const B: &'static str, const R: &'static str> = T;

                fn f() ->i32{ (3 as Refinement<i32, "x", "x > 2">) as Refinement<i32, "y", "y > 1"> }
            }
            .to_string(),
            |expr, tcx, local_ctx| {
                let conf = SmtConf::default_z3();
                let mut solver = conf.spawn(()).unwrap();
                solver.path_tee("/tmp/z3").unwrap();
                let ctx = RContext::new();
                let ty = type_of(expr, &tcx, &ctx, local_ctx, &mut solver).unwrap();
                pretty::assert_eq!(ty.to_string(), "ty!{ y : i32 | y > 1 }");
                info!("expr has type {}", ty);
            },
        )
        .unwrap();
    }

    #[test_log::test]
    fn test_type_function() {
        with_item(
            &quote! {
                type Refinement<T, const B: &'static str, const R: &'static str> = T;

                fn f(a : Refinement<i32, "x", "x > 1">) -> Refinement<i32, "v", "v > 0"> {
                    a
                }
            }
            .to_string(),
            |item, tcx| {
                let ty = type_check_function(item, &tcx).unwrap();
                pretty::assert_eq!(ty.to_string(), "ty!{ v : i32 | v > 0 }");
            },
        )
        .unwrap();
    }

    #[should_panic]
    #[test_log::test]
    fn test_type_function_invalid() {
        with_item(
            &quote! {
                type Refinement<T, const B: &'static str, const R: &'static str> = T;

                fn f(a : Refinement<i32, "x", "x > 0">) -> Refinement<i32, "v", "v > 1"> {
                    a
                }
            }
            .to_string(),
            |item, tcx| {
                let ty = type_check_function(item, &tcx).unwrap();
                pretty::assert_eq!(ty.to_string(), "ty!{ v : i32 | v > 0 }");
            },
        )
        .unwrap();
    }

    #[test_log::test]
    fn test_var_with_eq() {
        with_item(
            &quote! {
                type Refinement<T, const B: &'static str, const R: &'static str> = T;

                fn f(a : Refinement<i32, "av", "true">) -> Refinement<i32, "v", "v == av"> {
                    a
                }
            }
            .to_string(),
            |item, tcx| {
                let ty = type_check_function(item, &tcx).unwrap();
                pretty::assert_eq!(ty.to_string(), "ty!{ v : i32 | v == av }");
            },
        )
        .unwrap();
    }

    #[should_panic]
    #[test_log::test]
    fn test_var_with_eq_neg() {
        with_item(
            &quote! {
                type Refinement<T, const B: &'static str, const R: &'static str> = T;

                fn f(a : Refinement<i32, "av", "true">) -> Refinement<i32, "v", "v == av + 1"> {
                    a
                }
            }
            .to_string(),
            |item, tcx| {
                let _ty = type_check_function(item, &tcx).unwrap();
            },
        )
        .unwrap();
    }

    #[test_log::test]
    fn test_type_ite() {
        with_item(
            &quote! {
                type Refinement<T, const B: &'static str, const R: &'static str> = T;

                fn f(a : Refinement<i32, "x", "x > 0">) -> Refinement<i32, "v", "v > 0"> {
                    if true { a } else { a }
                }
            }
            .to_string(),
            |item, tcx| {
                let conf = SmtConf::default_z3();
                let mut solver = conf.spawn(()).unwrap();
                solver.path_tee("/tmp/z3").unwrap();
                let ty = type_check_function(item, &tcx).unwrap();
                pretty::assert_eq!(ty.to_string(), "ty!{ v : i32 | v > 0 }");
            },
        )
        .unwrap();
    }
}
