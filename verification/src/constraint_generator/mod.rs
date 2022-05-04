use std::io::Write;
use std::time::SystemTime;

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
use syn::Token;
use tracing::error;

use syn::parse_quote;
use tracing::info;
use tracing::instrument;
use tracing::trace;

pub struct Fresh {
    current: u32,
}

impl Fresh {
    fn new() -> Self {
        Fresh { current: 0 }
    }

    fn fresh_ident(&mut self) -> String {
        let counter = self.current;
        self.current += 1;
        format!("_{}", counter)
    }
}

#[cfg(test)]
mod tests;

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

                ctx.add_ty(param.pat.hir_id, refinement)
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
            solver
                .path_tee(format!("/tmp/z3-fn-{:?}.lisp", SystemTime::now()))
                .unwrap();

            let mut fresh = Fresh::new();

            let actual_ty = type_of_mut(
                &body.value,
                &tcx,
                &mut ctx,
                local_ctx,
                &mut solver,
                &mut fresh,
            )?;
            //TODO: check actual_ctx ≼ parameter_after_ctx

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

pub fn transition_stmt<'a, 'b, 'c, 'd, 'tcx, P>(
    stmts: &'a [hir::Stmt<'tcx>],
    tcx: &'b TyCtxt<'tcx>,
    ctx: &'c mut RContext<'a>,
    local_ctx: &'a TypeckResults<'a>,
    solver: &mut Solver<P>,
    fresh: &mut Fresh,
) -> anyhow::Result<()>
where
    // 'tcx at least as long as 'a
    'tcx: 'a,
    // 'a at least as long as 'c
    'a: 'c,
{
    for stmt in stmts {
        match stmt.kind {
            hir::StmtKind::Local(local) => {
                let initializer = local.init.ok_or(anyhow!(
                    "All declarations are expected to contain initializers"
                ))?;

                let type_of_init = type_of_mut(initializer, tcx, ctx, local_ctx, solver, fresh)?;
                assert!(
                    local.ty.is_none(),
                    "Type Annotations on `let` not yet supported"
                );
                if let hir::PatKind::Binding(
                    hir::BindingAnnotation::Mutable | hir::BindingAnnotation::Unannotated,
                    _,
                    _,
                    None,
                ) = local.pat.kind
                {
                } else {
                    panic!(
                        "Only `let <var>` assignment supported at the moment, but got {:?}",
                        local.pat.kind
                    )
                }
                trace!(
                    "adding type {} to local {:?} in ctx. Stmt hir id: {}",
                    &type_of_init,
                    &local,
                    local.pat.hir_id
                );
                ctx.add_ty(local.pat.hir_id, type_of_init.clone());
                type_of_init
            }
            hir::StmtKind::Item(_) => todo!(),
            hir::StmtKind::Expr(inner_expr) => {
                type_of_mut(inner_expr, tcx, ctx, &local_ctx, solver, fresh)?
            }
            hir::StmtKind::Semi(inner_expr) => {
                type_of_mut(inner_expr, tcx, ctx, &local_ctx, solver, fresh)?
            }
            // _ => todo!()
        };
        trace!(ctx=%ctx.with_tcx(&tcx), "stmt transition: current ctx is");
    }

    anyhow::Ok(())
}

/// Computes the type of [`expr`] and returns the it, together with the ctx after execution
pub fn type_of<'a, 'b, 'c, 'tcx, P>(
    expr: &'a Expr<'tcx>,
    tcx: &'b TyCtxt<'tcx>,
    ctx: &'c RContext<'a>,
    local_ctx: &'a TypeckResults<'a>,
    solver: &mut Solver<P>,
    fresh: &mut Fresh,
) -> anyhow::Result<(RefinementType<'a>, RContext<'a>)>
where
    // 'tcx at least as long as 'a
    'tcx: 'a,
    // 'a at least as long as 'c
    'a: 'c,
{
    let mut ctx_after = ctx.clone();
    let ty = type_of_mut(expr, tcx, &mut ctx_after, local_ctx, solver, fresh)?;
    Ok((ty, ctx_after))
}

/// Computes the type of [`expr`], but mutates the `ctx` according to the execution
pub fn type_of_mut<'a, 'b, 'c, 'tcx, P>(
    expr: &'a Expr<'tcx>,
    tcx: &'b TyCtxt<'tcx>,
    ctx: &'c mut RContext<'a>,
    local_ctx: &'a TypeckResults<'a>,
    solver: &mut Solver<P>,
    fresh: &mut Fresh,
) -> anyhow::Result<RefinementType<'a>>
where
    // 'tcx at least as long as 'a
    'tcx: 'a,
    // 'a at least as long as 'c
    'a: 'c,
{
    match &expr.kind {
        ExprKind::Lit(Spanned { node: _, span: _ }) => {
            let lit: syn::Expr = syn::parse_str(&expr.pretty_print())?;
            let ident = quote::format_ident!("{}", fresh.fresh_ident());
            let predicate = parse_quote! {
                #ident == #lit
            };
            trace!(pred=?predicate, "Expr Literal gets predicate");
            let base = local_ctx.node_type(expr.hir_id);

            anyhow::Ok(RefinementType {
                base,
                binder: ident.to_string(),
                predicate,
            })
        }
        ExprKind::Block(hir::Block { stmts, expr, .. }, None) => {
            transition_stmt(stmts, tcx, ctx, local_ctx, solver, fresh)?;
           
            match expr {
                Some(expr) => type_of_mut(
                    expr, tcx, /* todo!() */ ctx, /*&ctx_for_expr*/
                    local_ctx, solver, fresh,
                ),
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
            // Generates constraint `_7: i32 | _7 > 0 && av == _7`
            //
            let res = local_ctx.qpath_res(&path, expr.hir_id);
            match res {
                hir::def::Res::Local(hir_id) => {
                    let ty_in_context = ctx.lookup_hir(&hir_id).ok_or(anyhow!(
                        "could not find refinement type definition of {} in refinement context",
                        tcx.hir().node_to_string(hir_id)
                    ))?;
                    let new_name = fresh.fresh_ident();
                    let var_ty = ty_in_context.rename_binder(&new_name)?;
                    let combined_predicate = {
                        let new_pred = &var_ty.predicate;
                        let new_name = format_ident!("{}", &var_ty.binder);
                        let old_name = format_ident!("{}", &ty_in_context.binder);
                        parse_quote! {
                            #new_pred && #new_name == #old_name
                        }
                    };
                    let var_ty_with_eq_constraint = RefinementType {
                        predicate: combined_predicate,
                        ..var_ty
                    };
                    Ok(var_ty_with_eq_constraint)
                }
                hir::def::Res::Def(_, _) => todo!(),
                other => anyhow::bail!("reference to unexpected resolution {:?}", other),
            }
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
                    binder: fresh.fresh_ident(),
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
            let expr_ty = type_of_mut(expr, tcx, ctx, local_ctx, solver, fresh)?;

            let super_ty = RefinementType::from_type_alias(cast_ty, tcx, local_ctx.expr_ty(&expr))?;

            // SMT Subtyping
            // Why ctx_after_expr vs. ctx: For `a += 2 as ty!{v | v > 2}`, Type of `a += 2` will need to be a subtype
            // in the context of its execution effect (\Gamma' i.e. ctx_after_expr)
            require_is_subtype_of(&expr_ty, &super_ty, &ctx, solver)?;

            anyhow::Ok(super_ty)
        }
        ExprKind::Type(_, _) => todo!(),
        ExprKind::DropTemps(_) => todo!(),
        ExprKind::If(cond, then_expr, maybe_else_expr) => match maybe_else_expr {
            Some(else_expr) => {
                trace!(
                    cond=%cond.pretty_print(),
                    then_expr=%then_expr.pretty_print(),
                    else_expr=%else_expr.pretty_print(),
                    "typing cond:"
                );
                solver.comment("< typing if expr >").into_anyhow()?;

                // type check then_expr
                let mut then_ctx_before = ctx.clone();
                let then_cond = symbolic_execute(&cond, tcx, ctx, local_ctx)?;
                then_ctx_before.add_formula(then_cond);
                let (then_ty, then_ctx) =
                    type_of(then_expr, tcx, &then_ctx_before, local_ctx, solver, fresh)?;
                trace!(?then_ctx, "then_ctx");

                // type check else_expr
                let mut else_ctx_before = ctx.clone();
                let syn_cond: syn::Expr = symbolic_execute(&cond, tcx, ctx, local_ctx)?;
                let else_cond = syn::parse_quote! { ! (#syn_cond) };
                else_ctx_before.add_formula(else_cond);
                let (else_ty, else_ctx) =
                    type_of(else_expr, tcx, &else_ctx_before, local_ctx, solver, fresh)?;
                trace!(?else_ctx, "else_ctx");

                // We try to be a little clever here:
                // instead of requiring the user to specify the type of the if-then-else expression all the time
                // we make sure that it is sufficient, that either one of the branches has a general enough type to
                // cover both.
                // This means, that either else_ty ≼ then_ty OR then_ty ≼ else_ty. The complete expression
                // then has the lesser of both types.
                // subtype checking is done in the refinement type context of the subtype, because
                // it needs to show, that it is a sub type of the postulated complete type *in its context*

                let complete_ty = if let Ok(()) =
                    require_is_subtype_of(&else_ty, &then_ty, &else_ctx, solver)
                {
                    if let Ok(()) = is_sub_context(&else_ctx, &then_ctx) {
                        then_ty
                    } else {
                        anyhow::bail!(
                            "types follow the sub typing constraints, but their contexts do not"
                        )
                    }
                } else if let Ok(()) = require_is_subtype_of(&then_ty, &else_ty, &then_ctx, solver)
                {
                    *ctx = else_ctx;
                    if let Ok(()) = is_sub_context(&then_ctx, &ctx) {
                        else_ty
                    } else {
                        anyhow::bail!(
                            "types follow the sub typing constraints, but their contexts do not"
                        )
                    }
                } else {
                    anyhow::bail!("Error while typing the if-then-else expression: Neither else_ty ≼ then_ty nor then_ty ≼ else_ty. (then_ty: {}, else_ty: {})", then_ty, else_ty)
                };
                trace!(%complete_ty, "condition has type");
                solver.comment("</ typing if expr >").into_anyhow()?;
                anyhow::Ok(complete_ty)
            }
            None => todo!("missing else branch not supported yet"),
        },
        ExprKind::Loop(_, _, _, _) => todo!(),
        ExprKind::Match(_, _, _) => todo!(),
        ExprKind::Closure(_, _, _, _, _) => todo!(),
        ExprKind::Assign(lhs, rhs, _span) => match &lhs.kind {
            ExprKind::Path(path) => {
                let res = local_ctx.qpath_res(&path, lhs.hir_id);
                match res {
                    hir::def::Res::Local(hir_id) => {
                        let rhs_ty = type_of_mut(rhs, tcx, ctx, local_ctx, solver, fresh)?;
                        ctx.update_ty(hir_id, rhs_ty.clone());
                        trace!(%rhs_ty, "rhs_ty is");
                        anyhow::Ok(rhs_ty)
                    }
                    hir::def::Res::Def(_, _) => todo!(),
                    other => anyhow::bail!("reference to unexpected resolution {:?}", other),
                }
            }
            other => todo!(),
        },
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

fn is_sub_context<'tcx>(
    super_ctx: &RContext<'tcx>,
    sub_ctx: &RContext<'tcx>,
) -> anyhow::Result<()> {
    //TODO
    Ok(())
}

/// This executes e.g. a condition in an if-then-else expression to be used as
/// as formula in smt
/// In our case, symbolic executing entails replacing variable references (like `a`)
/// with their refinement type binder (like `av`)
/// Example
/// ```no run
/// fn f(a: ty!{av: i32 | ...}) {
///     if a {...} else {...}
/// }
/// ```
fn symbolic_execute<'a, 'b, 'c, 'tcx>(
    expr: &'a Expr<'tcx>,
    tcx: &'b TyCtxt<'tcx>,
    ctx: &'c RContext<'a>,
    local_ctx: &'a TypeckResults<'a>,
) -> anyhow::Result<syn::Expr> {
    match &expr.kind {
        ExprKind::Box(_) => todo!(),
        ExprKind::ConstBlock(_) => todo!(),
        ExprKind::Array(_) => todo!(),
        ExprKind::Call(_, _) => todo!(),
        ExprKind::MethodCall(_, _, _) => todo!(),
        ExprKind::Tup(_) => todo!(),
        ExprKind::Binary(Spanned { node: bin_op, .. }, left, right) => {
            let syn_op = syn::parse_str::<syn::BinOp>(bin_op.as_str())?;
            let left_syn = symbolic_execute(left, tcx, ctx, local_ctx)?;
            let right_syn = symbolic_execute(right, tcx, ctx, local_ctx)?;
            Ok(syn::Expr::Binary(syn::ExprBinary {
                attrs: vec![],
                left: Box::new(left_syn),
                op: syn_op,
                right: Box::new(right_syn),
            }))
        }
        ExprKind::Unary(_, _) => todo!(),
        ExprKind::Lit(_) => {
            let lit = syn::parse_str(&expr.pretty_print())?;
            Ok(lit)
        }
        ExprKind::Cast(_, _) => todo!(),
        ExprKind::Type(_, _) => todo!(),
        ExprKind::DropTemps(expr) => {
            trace!(?expr, "drop temps: ");
            symbolic_execute(expr, tcx, ctx, local_ctx)
        }
        ExprKind::Let(_) => todo!(),
        ExprKind::If(_, _, _) => todo!(),
        ExprKind::Loop(_, _, _, _) => todo!(),
        ExprKind::Match(_, _, _) => todo!(),
        ExprKind::Closure(_, _, _, _, _) => todo!(),
        ExprKind::Block(_, _) => todo!(),
        ExprKind::Assign(_, _, _) => todo!(),
        ExprKind::AssignOp(_, _, _) => todo!(),
        ExprKind::Field(_, _) => todo!(),
        ExprKind::Index(_, _) => todo!(),
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
            let res = local_ctx.qpath_res(&path, expr.hir_id);
            match res {
                hir::def::Res::Local(hir_id) => {
                    let ty_in_context = ctx.lookup_hir(&hir_id).ok_or(anyhow!(
                        "could not find refinement type definition of {:?} in refinement context",
                        hir_id
                    ))?;
                    trace!(?ty_in_context, "found refinement type:");

                    let refinement_ident = format_ident!("{}", &ty_in_context.binder);
                    Ok(parse_quote! { #refinement_ident })
                }
                hir::def::Res::Def(_, _) => todo!(),
                other => anyhow::bail!("reference to unexpected resolution {:?}", other),
            }
        }
        ExprKind::AddrOf(_, _, _) => todo!(),
        ExprKind::Break(_, _) => todo!(),
        ExprKind::Continue(_) => todo!(),
        ExprKind::Ret(_) => todo!(),
        ExprKind::InlineAsm(_) => todo!(),
        ExprKind::Struct(_, _, _) => todo!(),
        ExprKind::Repeat(_, _) => todo!(),
        ExprKind::Yield(_, _) => todo!(),
        ExprKind::Err => todo!(),
    }
}

#[instrument(skip_all, fields(%sub_ty, %super_ty))]
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
    solver
        .assert(refinements::encode_smt(&sub_ty.predicate))
        .into_anyhow()?;

    solver
        .declare_const(&super_ty.binder, "Int")
        .into_anyhow()?;

    solver
        .assert(format!("(= {} {})", &super_ty.binder, &sub_ty.binder))
        .into_anyhow()?;

    solver
        .assert(format!(
            "(not {})",
            refinements::encode_smt(&super_ty.predicate)
        ))
        .into_anyhow()?;

    solver
        .comment(&format!("checking: {} ≼  {}", sub_ty, super_ty))
        .into_anyhow()?;
    solver.flush()?;
    trace!("checking: {} ≼  {}", sub_ty, super_ty);
    let is_sat = solver.check_sat().into_anyhow()?;
    solver
        .comment(&format!("done! is sat: {}", is_sat))
        .into_anyhow()?;

    solver.pop(2).into_anyhow()?;
    solver.comment(&"-".repeat(80)).into_anyhow()?;
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
