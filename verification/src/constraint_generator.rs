use std::collections::HashMap;
use std::io::Write;
use std::time::SystemTime;

use crate::buildin_functions::CtxSpecFunctions;
use crate::refinement_context::is_sub_context;
use crate::refinement_context::RContext;
use crate::refinements;
use crate::refinements::MutRefinementType;
use crate::smtlib_ext::SmtResExt;
use anyhow::anyhow;

use hir::LoopSource;
use quote::format_ident;
use rsmt2::SmtConf;
use rsmt2::Solver;
use rustc_hir as hir;

use quote::quote;
use rustc_hir::{Expr, ExprKind};
use rustc_middle::ty::TyCtxt;
use rustc_middle::ty::TypeckResults;
use rustc_span::source_map::Spanned;
use tracing::error;
use tracing::Level;

use syn::parse_quote;
use tracing::info;
use tracing::instrument;
use tracing::span;
use tracing::trace;
use tracing::warn;

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
            ident,
            def_id,
            ..
        } => {
            trace!(node_to_string=?tcx.hir().node_to_string(function.hir_id()), "just for fun: print");
            let body = tcx.hir().body(body_id.clone());

            info!(?ident.name);
            trace!(?body_id, ?body, "function body");
            trace!(?function, "full function");
            let local_ctx = tcx.typeck(*def_id);

            // Get middle::ty of function
            let sigs = local_ctx.liberated_fn_sigs();
            let fn_sig = sigs
                .get(function.hir_id())
                .ok_or(anyhow!("function not found in typeck result"))?;
            trace!(?fn_sig);

            if CtxSpecFunctions::is_buildin(&ident.name.to_string()) {
                let out_ty = fn_sig.output();
                return anyhow::Ok(RefinementType {
                    base: out_ty,
                    binder: "v".to_string(),
                    predicate: parse_quote! { true },
                });
            }

            // get refinements for inputs
            let mut ctx = RContext::<hir::HirId>::new();
            let mut expected_end_state = RContext::<hir::HirId>::new();
            for ((hir_ty, middle_ty), param) in inputs.iter().zip(fn_sig.inputs()).zip(body.params)
            {
                let start_refinement =
                    match RefinementType::from_type_alias(hir_ty, &tcx, middle_ty.clone()) {
                        Ok(refinement) => {
                            trace!(%refinement, %param.pat.hir_id, "immut input type");
                            // Because mutable end-states may refer to immutable refinement binders
                            // we need to add them to the end ctx.
                            // Because immut types cannot chnge their predicates, the end state will need
                            // to have the same predicate as before.
                            // We could also use `ty!{ _ | true }}` here
                            expected_end_state.add_ty(param.pat.hir_id, refinement.clone());
                            refinement
                        }
                        Err(_) => {
                            let MutRefinementType { start, end } =
                                MutRefinementType::from_type_alias(
                                    hir_ty,
                                    &tcx,
                                    middle_ty.clone(),
                                )?;
                            expected_end_state.add_ty(param.pat.hir_id, end);
                            start
                        }
                    };
                ctx.add_ty(param.pat.hir_id, start_refinement)
            }

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
                .path_tee(format!("/tmp/z3-fn-{:?}.lisp", uuid::Uuid::new_v4()))
                .unwrap();

            let mut fresh = Fresh::new();

            let (actual_ty, ctx_after) = type_of(
                &body.value,
                &tcx,
                &mut ctx,
                local_ctx,
                &mut solver,
                &mut fresh,
            )?;

            // let actual_end_state =
            //     ctx_after.filter_hirs(|id| expected_end_state.types.contains_key(id));

            let span = span!(Level::INFO, "check_function_end").entered();

            is_sub_context(&expected_end_state, &ctx_after, tcx, &mut solver)?;

            trace!(%actual_ty, "actual function type");
            require_is_subtype_of(&actual_ty, &expected_type, &ctx_after, tcx, &mut solver)?;

            span.exit();

            anyhow::Ok(expected_type)
        }
        other => Err(anyhow!(
            "tried to type check a function, but got a {:?} instead",
            other
        )),
    }
}

#[instrument(skip_all)]
pub fn transition_stmt<'a, 'b, 'c, 'd, 'tcx, P>(
    stmts: &'a [hir::Stmt<'tcx>],
    tcx: &'b TyCtxt<'tcx>,
    ctx: &'c RContext<'tcx>,
    local_ctx: &'a TypeckResults<'tcx>,
    solver: &mut Solver<P>,
    fresh: &mut Fresh,
) -> anyhow::Result<RContext<'tcx>>
where
    // 'tcx at least as long as 'a
    'tcx: 'a,
    // 'a at least as long as 'c
    'a: 'c,
{
    let mut curr_ctx = ctx.clone();
    for stmt in stmts {
        curr_ctx = match stmt.kind {
            hir::StmtKind::Local(local) => {
                let initializer = local.init.ok_or(anyhow!(
                    "All declarations are expected to contain initializers"
                ))?;

                let (type_of_init, mut ctx_after) =
                    type_of(initializer, tcx, &curr_ctx, local_ctx, solver, fresh)?;
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
                ctx_after.add_ty(local.pat.hir_id, type_of_init.clone());
                ctx_after
            }
            hir::StmtKind::Item(_) => todo!(),
            hir::StmtKind::Expr(inner_expr) => {
                type_of(inner_expr, tcx, &curr_ctx, &local_ctx, solver, fresh)?.1
            }
            hir::StmtKind::Semi(inner_expr) => {
                type_of(inner_expr, tcx, &curr_ctx, &local_ctx, solver, fresh)?.1
            } // _ => todo!()
        };
        let pretty_stmt =
            rustc_hir_pretty::to_string(&rustc_hir_pretty::NoAnn, |state| state.print_stmt(stmt));

        trace!(stmt=%pretty_stmt, ctx_after=%curr_ctx.with_tcx(&tcx), "stmt transition: current ctx is");
    }

    anyhow::Ok(curr_ctx)
}

fn negate_predicate(pred: syn::Expr) -> anyhow::Result<syn::Expr> {
    let not = syn::parse_str::<syn::UnOp>("!")?;
    Ok(syn::Expr::Unary(syn::ExprUnary {
        attrs: Vec::new(),
        op: not,
        expr: Box::new(pred),
    }))
}

/// Computes the type of [`expr`], but mutates the `ctx` according to the execution
#[instrument(skip_all, fields(expr=?expr.pretty_print()))]
pub fn type_of<'a, 'b, 'c, 'tcx, P>(
    expr: &'a Expr<'tcx>,
    tcx: &'b TyCtxt<'tcx>,
    ctx: &'c RContext<'tcx>,
    local_ctx: &'a TypeckResults<'tcx>,
    solver: &mut Solver<P>,
    fresh: &mut Fresh,
) -> anyhow::Result<(RefinementType<'tcx>, RContext<'tcx>)>
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
            trace!(pred=%quote! { #predicate }, "Expr Literal gets predicate");
            let base = local_ctx.node_type(expr.hir_id);

            anyhow::Ok((
                RefinementType {
                    base,
                    binder: ident.to_string(),
                    predicate,
                },
                ctx.clone(),
            ))
        }
        ExprKind::Block(hir::Block { stmts, expr, .. }, None) => {
            let ctx_after_stmts = transition_stmt(stmts, tcx, ctx, local_ctx, solver, fresh)?;

            match expr {
                Some(expr) => type_of(expr, tcx, &ctx_after_stmts, local_ctx, solver, fresh),
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
            let dest_hir_id = expr.try_into_path_hir_id(tcx, local_ctx)?;
            let ty_in_context = ctx.lookup_hir(&dest_hir_id).ok_or(anyhow!(
                "could not find refinement type definition of {} in refinement context",
                tcx.hir().node_to_string(dest_hir_id)
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
            Ok((var_ty_with_eq_constraint, ctx.clone()))
        }
        ExprKind::Box(_) => todo!(),
        ExprKind::ConstBlock(_) => todo!(),
        ExprKind::Array(_) => todo!(),
        ExprKind::Call(func, args) => {
            let path_hir_id = func.try_into_path_hir_id(tcx, local_ctx)?;
            let func_decl = tcx.hir().get(path_hir_id);

            enum FnCallType<'tcx> {
                AssertCtx(RContext<'tcx, hir::HirId>),
                UpdateCtx(RContext<'tcx, hir::HirId>),
                NormalCall,
            }
            let fn_type = match func_decl
                .ident()
                .expect("func decl must have an ident()")
                .name
                .to_string()
                .as_ref()
            {
                "assert_ctx" => FnCallType::AssertCtx(
                    RContext::<hir::HirId>::try_from_assert_expr(args, tcx, local_ctx)?,
                ),
                "update_ctx" => FnCallType::UpdateCtx(
                    RContext::<hir::HirId>::try_from_assert_expr(args, tcx, local_ctx)?,
                ),
                _ => FnCallType::NormalCall,
            };

            match fn_type {
                FnCallType::AssertCtx(assert_ctx) => {
                    // do sub typing checkings
                    trace!(ctx=%assert_ctx.with_tcx(tcx), "found ctx assertion");
                    is_sub_context(ctx, &assert_ctx, tcx, solver)?;
                    is_sub_context(&assert_ctx, ctx, tcx, solver)?;

                    anyhow::Ok((
                        RefinementType::new_empty_refinement_for(
                            expr,
                            local_ctx,
                            fresh.fresh_ident(),
                        ),
                        ctx.clone(),
                    ))
                }
                FnCallType::UpdateCtx(spec_ctx) => {
                    // do sub typing checkings
                    trace!(ctx=%spec_ctx.with_tcx(tcx), "found ctx update");
                    is_sub_context(&spec_ctx, ctx, tcx, solver)?;

                    anyhow::Ok((
                        RefinementType::new_empty_refinement_for(
                            expr,
                            local_ctx,
                            fresh.fresh_ident(),
                        ),
                        spec_ctx,
                    ))
                }
                FnCallType::NormalCall => {
                    todo!("do normal function handling")
                }
            }
        }
        ExprKind::MethodCall(_, _, _) => todo!(),
        ExprKind::Tup(contents) => {
            let ty = match contents {
                [] => {
                    RefinementType::new_empty_refinement_for(expr, local_ctx, fresh.fresh_ident())
                }
                _o => todo!(),
            };
            anyhow::Ok((ty, ctx.clone()))
        }
        ExprKind::Binary(Spanned { node: _bin_op, .. }, left, right) => {
            let sym = symbolic_execute(expr, tcx, ctx, local_ctx)?;
            let ident = fresh.fresh_ident();
            let new_name = format_ident!("{}", &ident);

            let (_ty_left, ctx_after_left) = type_of(left, tcx, ctx, local_ctx, solver, fresh)?;
            let (_ty_right, ctx_after_right) =
                type_of(right, tcx, &ctx_after_left, local_ctx, solver, fresh)?;
            let ty = RefinementType {
                base: local_ctx.expr_ty(expr),
                binder: ident,
                predicate: parse_quote! {
                    #sym == #new_name
                },
            };
            trace!(%ty,"type of binary expr");

            //TODO check no mut in expr
            anyhow::Ok((ty, ctx_after_right))
        }
        ExprKind::Unary(hir::UnOp::Deref, expr) => {
            type_of(expr, tcx, ctx, local_ctx, solver, fresh)
        }
        ExprKind::Unary(_, _) => todo!(),
        ExprKind::Cast(expr, cast_ty) => {
            // Generate sub-typing constraint
            let (expr_ty, ctx_after) = type_of(expr, tcx, ctx, local_ctx, solver, fresh)?;

            let super_ty = RefinementType::from_type_alias(cast_ty, tcx, local_ctx.expr_ty(&expr))?;

            // SMT Subtyping
            // Why ctx_after_expr vs. ctx: For `a += 2 as ty!{v | v > 2}`, Type of `a += 2` will need to be a subtype
            // in the context of its execution effect (\Gamma' i.e. ctx_after_expr)
            require_is_subtype_of(&expr_ty, &super_ty, &ctx, tcx, solver)?;

            anyhow::Ok((super_ty, ctx_after))
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
                let then_cond: syn::Expr = symbolic_execute(&cond, tcx, ctx, local_ctx)?;
                then_ctx_before.push_formula(then_cond.clone());
                let (then_ty, then_ctx) =
                    type_of(then_expr, tcx, &then_ctx_before, local_ctx, solver, fresh)?;
                trace!(?then_ctx, "then_ctx");

                // type check else_expr
                let mut else_ctx_before = ctx.clone();
                let syn_cond: syn::Expr = symbolic_execute(&cond, tcx, ctx, local_ctx)?;
                let else_cond = negate_predicate(syn_cond)?;
                info!(else_cond=%quote!{#else_cond}, "else_cond_formula: ");

                else_ctx_before.push_formula(else_cond.clone());
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

                let (complete_ty, ctx_after) = if let Ok(()) =
                    require_is_subtype_of(&else_ty, &then_ty, &else_ctx, tcx, solver)
                {
                    match is_sub_context(
                        &else_ctx.pop_formula(),
                        &then_ctx.pop_formula(),
                        tcx,
                        solver,
                    ) {
                        Ok(()) => (then_ty, else_ctx.pop_formula()),
                        Err(err) => anyhow::bail!(
                            "types follow the sub typing constraints, but their contexts do not {}",
                            err
                        ),
                    }
                } else if let Ok(()) =
                    require_is_subtype_of(&then_ty, &else_ty, &then_ctx, tcx, solver)
                {
                    match is_sub_context(
                        &then_ctx.pop_formula(),
                        &else_ctx.pop_formula(),
                        tcx,
                        solver,
                    ) {
                        Ok(()) => (else_ty, then_ctx.pop_formula()),
                        Err(err) => anyhow::bail!(
                            "types follow the sub typing constraints, but their contexts do not {}",
                            err
                        ),
                    }
                } else {
                    anyhow::bail!("Error while typing the if-then-else expression: Neither else_ty ≼ then_ty nor then_ty ≼ else_ty. (then_ty: {}, else_ty: {})", then_ty, else_ty)
                };
                trace!(%complete_ty, "condition has type");
                solver.comment("</ typing if expr >").into_anyhow()?;
                anyhow::Ok((complete_ty, ctx_after))
            }
            None => todo!("missing else branch not supported yet"),
        },
        ExprKind::Loop(
            hir::Block {
                stmts: [],
                expr: Some(expr),
                ..
            },
            None,
            LoopSource::While,
            _,
        ) => {
            let (ctx_bang, while_cond) = match &expr.kind {
                ExprKind::If(cond, then_expr, Some(else_expr)) => {
                    match &else_expr.kind {
                        ExprKind::Block(
                            hir::Block {
                                stmts:
                                    [hir::Stmt {
                                        kind: hir::StmtKind::Expr(Expr { kind: a, .. }),
                                        ..
                                    }],
                                ..
                            },
                            None,
                        ) => (),
                        _other => panic!("unexpected else branch in loop: was not {{break;}}"),
                    }

                    let mut then_ctx_before = ctx.clone();
                    let then_cond: syn::Expr = symbolic_execute(&cond, tcx, ctx, local_ctx)?;
                    then_ctx_before.push_formula(then_cond.clone());

                    let (_ty, ctx_after) =
                        type_of(then_expr, tcx, &then_ctx_before, local_ctx, solver, fresh)?;
                    // pop `then_cond` off the path stack
                    let ctx_bang_tick = ctx_after.pop_formula();
                    is_sub_context(ctx, &ctx_bang_tick, tcx, solver)?;
                    (ctx_bang_tick, then_cond)
                }
                _other => todo!(),
            };

            let refined_unit_type =
                RefinementType::new_empty_refinement_for(expr, local_ctx, fresh.fresh_ident());

            let exit_path_formula = negate_predicate(while_cond)?;

            let mut ctx_after = ctx_bang.clone();
            ctx_after.push_formula(exit_path_formula);
            Ok((refined_unit_type, ctx_after))
        }
        ExprKind::Loop(_, _, _, _) => todo!(),
        ExprKind::Match(_, _, _) => todo!(),
        ExprKind::Closure(_, _, _, _, _) => todo!(),
        ExprKind::Assign(lhs, rhs, _span) => {
            let dest_hir_id = match &lhs.kind {
                ExprKind::Path(_path) => lhs.try_into_path_hir_id(tcx, local_ctx)?,
                ExprKind::Unary(hir::UnOp::Deref, inner) => {
                    inner.try_into_path_hir_id(tcx, local_ctx)?
                }
                other => todo!("don't know how to assign to {:?}", other),
            };

            let (rhs_ty, mut after_rhs) = type_of(rhs, tcx, ctx, local_ctx, solver, fresh)?;
            let ty_in_context = ctx.lookup_hir(&dest_hir_id).ok_or(anyhow!(
                "could not find refinement type definition of {} in refinement context",
                tcx.hir().node_to_string(dest_hir_id)
            ))?;
            after_rhs.update_ty(dest_hir_id, rhs_ty.clone());
            trace!(%rhs_ty, after_rhs=%after_rhs.with_tcx(tcx), "rhs_ty is");
            anyhow::Ok((rhs_ty, after_rhs))
        }
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
#[instrument(skip_all)]
fn symbolic_execute<'a, 'b, 'c, 'tcx>(
    expr: &'a Expr<'tcx>,
    tcx: &'b TyCtxt<'tcx>,
    ctx: &'c RContext<'a>,
    local_ctx: &'a TypeckResults<'a>,
) -> anyhow::Result<syn::Expr> {
    // if expr.can_have_side_effects() {
    //     anyhow::bail!("Expr {} may have side-effects -> no symbolic exec possible", expr.pretty_print());
    // }
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
        ExprKind::Unary(op, inner) => {
            let syn_op = syn::parse_str::<syn::UnOp>(op.as_str())?;
            let inner_syn = symbolic_execute(inner, tcx, ctx, local_ctx)?;
            Ok(syn::Expr::Unary(syn::ExprUnary {
                attrs: vec![],
                expr: Box::new(inner_syn),
                op: syn_op,
            }))
        }
        ExprKind::Lit(_) => {
            let lit = syn::parse_str(&expr.pretty_print())?;
            Ok(lit)
        }
        ExprKind::Cast(_, _) => todo!(),
        ExprKind::Type(_, _) => todo!(),
        ExprKind::DropTemps(expr) => symbolic_execute(expr, tcx, ctx, local_ctx),
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
                    trace!(%ty_in_context, "found refinement type:");

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
    tcx: &TyCtxt<'tcx>,
    solver: &mut Solver<P>,
) -> anyhow::Result<()> {
    info!(
        "need to do subtyping judgement: {} ≼  {} in ctx {}",
        sub_ty,
        super_ty,
        ctx.with_tcx(tcx)
    );
    solver.comment("checking is_subtype_of").into_anyhow()?;
    solver.push(1).into_anyhow()?;
    ctx.encode_smt(solver, tcx)?;

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
        .comment(&format!("done checking is_subtype_of! is sat: {}", is_sat))
        .into_anyhow()?;

    solver.pop(2).into_anyhow()?;
    solver.comment(&"-".repeat(80)).into_anyhow()?;
    if is_sat {
        let msg = format!(
            "Subtyping judgement failed: {} is not a sub_ty of {}",
            &sub_ty, &super_ty
        );
        error!("{} in ctx {}", msg, ctx.with_tcx(tcx));
        Err(anyhow!(msg))?;
    } else {
        info!("no counterexample found 🮱")
        // no counterexample found => everything is fine => continue
    };
    Ok(())
}
