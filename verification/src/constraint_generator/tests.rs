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
            let (ty, ctx_after) = type_of(expr, &tcx, &ctx, local_ctx, &mut solver).unwrap();
            pretty::assert_eq!(ty.to_string(), "ty!{ v : i32 | v == 1 }");
            pretty::assert_eq!(ctx, ctx_after);
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
            let (ty, ctx_after) = type_of(expr, &tcx, &ctx, local_ctx, &mut solver).unwrap();
            pretty::assert_eq!(ty.to_string(), "ty!{ x : i32 | x > 0 }");
            pretty::assert_eq!(ctx, ctx_after);
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
            let (_ty, _ctx_after) = type_of(expr, &tcx, &ctx, local_ctx, &mut solver).unwrap();
            // ^- panic happens here
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
            let (ty, ctx_after) = type_of(expr, &tcx, &ctx, local_ctx, &mut solver).unwrap();
            pretty::assert_eq!(ty.to_string(), "ty!{ y : i32 | y > 1 }");
            pretty::assert_eq!(ctx, ctx_after);
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

#[should_panic]
#[test_log::test]
fn test_type_ite_neg_simple() {
    with_item(
        &quote! {
            type Refinement<T, const B: &'static str, const R: &'static str> = T;

            fn f(a : Refinement<i32, "x", "x > 0">) -> Refinement<i32, "v", "v > 0"> {
                if a > 1 { a } else { 0 as Refinement<i32, "y", "y > 0"> }
                //                    ^--- 0 does not have type v > 0
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
fn test_type_ite_partial() {
    with_item(
        &quote! {
            type Refinement<T, const B: &'static str, const R: &'static str> = T;

            fn f(a : Refinement<i32, "x", "x > 0">) -> Refinement<i32, "v", "v > 0"> {
                if a > 1 { a } else { 1 as Refinement<i32, "y", "y > 0"> }
                //         ^--- x > 1 |- {==x} ≼ {x > 0}
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
fn test_type_ite() {
    with_item(
        &quote! {
            type Refinement<T, const B: &'static str, const R: &'static str> = T;

            fn f(a : Refinement<i32, "x", "true">) -> Refinement<i32, "v", "v > 0"> {
                if a > 0 { a } else { 1 as Refinement<i32, "y", "y > 0"> }
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
fn test_type_ite_false() {
    with_item(
        &quote! {
            type Refinement<T, const B: &'static str, const R: &'static str> = T;

            fn f(a : Refinement<i32, "x", "x > 0">) -> Refinement<i32, "v", "v > 0"> {
                if false { 0 } else { 1 as Refinement<i32, "y", "y > 0"> }
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
fn test_type_ite_true_cond_by_ctx() {
    with_item(
        &quote! {
            type Refinement<T, const B: &'static str, const R: &'static str> = T;

            fn f(a : Refinement<i32, "x", "x > 0">) -> Refinement<i32, "v", "v > 0"> {
                if a > 0 { a } else { 0 }
                // ^^^^^ --- is always true in ctx `x > 0` => else branch can have any type
            }
        }
        .to_string(),
        |item, tcx| {
            let ty = type_check_function(item, &tcx).unwrap();
            pretty::assert_eq!(ty.to_string(), "ty!{ v : i32 | v > 0 }");
        },
    )
    .expect("Error running Rustc");
}

#[test_log::test]
fn test_type_max() {
    with_item(
        &quote! {
            type Refinement<T, const B: &'static str, const R: &'static str> = T;

            fn max(a : Refinement<i32, "av", "true">, b: Refinement<i32, "bv", "true">) -> Refinement<i32, "v", "v >= av && v >= bv"> {
                if a > b { a as Refinement<i32, "x", "x >= av && x >= bv"> } else { b }
            }
        }
        .to_string(),
        |item, tcx| {
            let ty = type_check_function(item, &tcx).unwrap();
            pretty::assert_eq!(ty.to_string(), "ty!{ v : i32 | v >= av && v >= bv }");
        },
    )
    .unwrap();
}

#[should_panic]
#[test_log::test]
fn test_type_max_neg() {
    with_item(
        &quote![
            type Refinement<T, const B: &'static str, const R: &'static str> = T;

            fn f(
                a: Refinement<i32, "av", "true">,
                b: Refinement<i32, "bv", "true">,
            ) -> Refinement<i32, "v", "v >= av && v < bv"> {
                if a > b {
                    a as Refinement<i32, "x", "x >= av && x < bv">
                } else {
                    b
                }
            }
        ]
        .to_string(),
        |item, tcx| {
            let ty = type_check_function(item, &tcx).unwrap();
            pretty::assert_eq!(ty.to_string(), "ty!{ v : i32 | v >= av && v >= bv }");
        },
    )
    .unwrap();
}
