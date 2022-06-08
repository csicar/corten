use super::*;
use crate::test_with_rustc::{with_expr, with_item_and_rt_lib};
use pretty_assertions as pretty;
use quote::quote;
use rsmt2::SmtConf;
use unindent::unindent;

fn init_tracing() {
    let subscriber = ::tracing_subscriber::FmtSubscriber::builder()
        .with_env_filter(::tracing_subscriber::EnvFilter::from_default_env())
        .pretty()
        .finish();
    ::tracing::subscriber::set_global_default(subscriber);
}

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
            #![feature(adt_const_params)]

            // type Refinement<T, const B: &'static str, const R: &'static str> = T;
            fn f() ->i32{ 1 }
        }
        .to_string(),
        |expr, tcx, local_ctx| {
            let conf = SmtConf::default_z3();
            let mut solver = conf.spawn(()).unwrap();

            let ctx = RContext::<hir::HirId>::new();

            let (ty, ctx_after) =
                type_of(expr, &tcx, &ctx, local_ctx, &mut solver, &mut Fresh::new()).unwrap();
            pretty::assert_eq!(ty.to_string(), "ty!{ _0 : i32 | _0 == 1 }");
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
            #![feature(adt_const_params)]

            type Refinement<T, const B: &'static str, const R: &'static str> = T;

            fn f() ->i32{ 1 as Refinement<i32, "x", "x > 0">}
        }
        .to_string(),
        |expr, tcx, local_ctx| {
            let conf = SmtConf::default_z3();
            let mut solver = conf.spawn(()).unwrap();
            solver.path_tee("/tmp/z3").unwrap();
            let ctx = RContext::<hir::HirId>::new();
            let (ty, ctx_after) =
                type_of(expr, &tcx, &ctx, local_ctx, &mut solver, &mut Fresh::new()).unwrap();
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
            #![feature(adt_const_params)]

            type Refinement<T, const B: &'static str, const R: &'static str> = T;

            fn f() -> i32 { 1 as Refinement<i32, "x", "x < 0"> }
        }
        .to_string(),
        |expr, tcx, local_ctx| {
            let conf = SmtConf::default_z3();
            let mut solver = conf.spawn(()).unwrap();
            solver.path_tee("/tmp/z3").unwrap();
            let ctx = RContext::<hir::HirId>::new();
            let mut ctx_after = ctx.clone();
            let _ty = type_of(expr, &tcx, &ctx, local_ctx, &mut solver, &mut Fresh::new()).unwrap();
            // ^- panic happens here
        },
    )
    .unwrap();
}

#[test_log::test]
fn test_subtype_lit_pos_nested() {
    with_expr(
        &quote! {
            #![feature(adt_const_params)]

            type Refinement<T, const B: &'static str, const R: &'static str> = T;

            fn f() ->i32{ (3 as Refinement<i32, "x", "x > 2">) as Refinement<i32, "y", "y > 1"> }
        }
        .to_string(),
        |expr, tcx, local_ctx| {
            let conf = SmtConf::default_z3();
            let mut solver = conf.spawn(()).unwrap();
            solver.path_tee("/tmp/z3").unwrap();
            let ctx = RContext::<hir::HirId>::new();

            let (ty, ctx_after) =
                type_of(expr, &tcx, &ctx, local_ctx, &mut solver, &mut Fresh::new()).unwrap();
            pretty::assert_eq!(ty.to_string(), "ty!{ y : i32 | y > 1 }");
            pretty::assert_eq!(ctx, ctx_after);
            info!("expr has type {}", ty);
        },
    )
    .unwrap();
}

#[test_log::test]
fn test_type_function() {
    with_item_and_rt_lib(
        &quote! {
            fn f(a : ty!{ x : i32 | x > 1 }) -> ty!{ v : i32 | v > 0 } {
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
    with_item_and_rt_lib(
        &quote! {
            fn f(a : ty!{ x : i32 | x > 0 }) -> ty!{ v : i32 | v > 1 } {
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
    with_item_and_rt_lib(
        &quote! {
            fn f(a : ty!{ av : i32 | true }) -> ty!{ v : i32 | v == av } {
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
    with_item_and_rt_lib(
        &quote! {
            fn f(a : ty!{ av : i32 | true }) -> ty!{ v : i32 | v == av + 1 } {
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
    with_item_and_rt_lib(
        &quote! {
            fn f(a : ty!{ x : i32 | x > 0 }) -> ty!{ v : i32 | v > 0 } {
                if a > 1 { a } else { 0 as ty!{ y : i32 | y > 0 } }
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
    with_item_and_rt_lib(
        &quote! {
            fn f(a : ty!{ x : i32 | x > 0 }) -> ty!{ v : i32 | v > 0 } {
                if a > 1 { a } else { 1 as ty!{ y : i32 | y > 0 } }
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
    with_item_and_rt_lib(
        &quote! {
            fn f(a : ty!{ x : i32 | true }) -> ty!{ v : i32 | v > 0 } {
                if a > 0 { a } else { 1 as ty!{ y : i32 | y > 0 } }
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
    with_item_and_rt_lib(
        &quote! {
            fn f(a : ty!{ x : i32 | x > 0 }) -> ty!{ v : i32 | v > 0 } {
                if false { 0 } else { 1 as ty!{ y : i32 | y > 0 } }
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
    with_item_and_rt_lib(
        &quote! {
            fn f(a : ty!{ x : i32 | x > 0 }) -> ty!{ v : i32 | v > 0 } {
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
    .unwrap();
}

#[test_log::test]
fn test_type_max() {
    with_item_and_rt_lib(
        &quote! {
            fn max(a : ty!{ av: i32 | true}, b: ty!{ bv: i32 | true}) -> ty!{ v: i32 | v >= av && v >= bv} {
                if a > b { a as ty!{ x : i32 | x >= av && x >= bv } } else { b }
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
    with_item_and_rt_lib(
        &quote![
            fn f(
                a: ty! { av : i32 | true },
                b: ty! { bv : i32 | true },
            ) -> ty! { v : i32 | v >= av && v < bv } {
                if a > b {
                    a as ty! { x : i32 | x >= av && x < bv }
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

/// Mutability
///

#[test_log::test]
fn test_assign_single() {
    with_expr(
        &quote! {
            #![feature(adt_const_params)]

            type Refinement<T, const B: &'static str, const R: &'static str> = T;

            fn f() ->i32{ let mut a = 3; a = 4; a = 8; 0 }
        }
        .to_string(),
        |expr, tcx, local_ctx| {
            let conf = SmtConf::default_z3();
            let mut solver = conf.spawn(()).unwrap();
            solver.path_tee("/tmp/z3").unwrap();
            let ctx = RContext::<hir::HirId>::new();

            let (ty, ctx_after) = type_of(expr, &tcx, &ctx, local_ctx, &mut solver, &mut Fresh::new()).unwrap();
            pretty::assert_eq!(ctx_after.with_tcx(&tcx).to_string(), unindent("
                RContext {
                    // formulas
                    // types
                    <fud.rs>:4:135: 4:140 (#0) local mut a (hir_id=HirId { owner: DefId(0:7 ~ rust_out[9149]::f), local_id: 4 }) : ty!{ _0 : i32 | _0 == 8 }
                }
                "));
            pretty::assert_eq!(ty.to_string(), "ty!{ _3 : i32 | _3 == 0 }");
            info!("expr has type {}", ty);
        },
    )
    .unwrap();
}

#[test_log::test]
fn test_assign_simple() {
    with_item_and_rt_lib(
        &quote! {
            fn max() -> ty!{ v : i32 | true } {
                let mut a = 7;
                a = 9;
                a
            }
        }
        .to_string(),
        |item, tcx| {
            let ty = type_check_function(item, &tcx).unwrap();
            pretty::assert_eq!(ty.to_string(), "ty!{ v : i32 | true }");
        },
    )
    .unwrap();
}

#[test_log::test]
fn test_assign_pred() {
    with_item_and_rt_lib(
        &quote! {
            fn max() -> ty!{ v : i32 | v == 9 } {
                let mut a = 7;
                a = 9;
                a
            }
        }
        .to_string(),
        |item, tcx| {
            let ty = type_check_function(item, &tcx).unwrap();
            pretty::assert_eq!(ty.to_string(), "ty!{ v : i32 | v == 9 }");
        },
    )
    .unwrap();
}

#[test_log::test]
fn test_assign_non_lit() {
    with_item_and_rt_lib(
        &quote! {
            fn max() -> ty!{ v : i32 | v > 0 } {
                let mut a = 7;
                let b  = 2 as ty!{ x : i32 | x > 0 };
                a = b;
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
fn test_assign_ite() {
    with_item_and_rt_lib(
        &quote! {
            fn max(b: ty!{ b : i32 | true }) -> ty!{ v : i32 | v > 0 } {
                let mut a = 2;
                if b <= 0 {
                    0
                } else {
                    a = b as ty!{ l : i32 | l > 0 }; 0
                };
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
fn test_assign_ite_neg() {
    with_item_and_rt_lib(
        &quote! {
            fn max(b: ty!{ b : i32 | true }) -> ty!{ v : i32 | v < 0 } {
                let mut a = 2;
                if b > 0 {
                    a = b; 0
                } else { 0
                };
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
#[test]
fn test_subtype_ctx_neg() {
    with_item_and_rt_lib(
        &quote! {
            fn max(b: ty!{ bv : i32 | true }) -> ty!{ v : i32 | v > 0 } {
                let mut a = 2;
                if b > 0 {
                    a = 0; 0
                    //- `a` is set to 0: contradicts "v > 0"
                } else { 0
                };
                a // but `a` is returned here
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

#[test]
fn test_subtype_ctx_pos() {
    init_tracing();
    with_item_and_rt_lib(
        &quote! {
            fn max(b: ty!{ b : i32 | true }) -> ty!{ v : i32 | v > 0 } {
                let mut a = 2;
                if !(b > 0) {
                    0
                } else {
                    a = b as ty!{ b2 : i32 | b2 > 0 };
                    0
                };
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

#[test]
fn test_update_type() {
    init_tracing();
    with_item_and_rt_lib(
        &quote! {
            fn f() -> ty!{ v : i32 | v > 0 } {
                let mut tmp = 2;
                tmp as ty!{ v1 : i32 | v1 > 0 };
                tmp
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

#[test]
fn test_update_incs() {
    init_tracing();
    with_item_and_rt_lib(
        &quote! {
            fn f() -> ty!{ v : i32 | v > 0 } {
                let mut tmp = 2 as ty!{tmp1 : i32 | tmp1 >= 0};
                tmp = (tmp + 1) as ty!{a: i32 | a > 0};
                tmp
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

#[test]
fn test_update_dependent_incs() {
    init_tracing();
    with_item_and_rt_lib(
        &quote! {
            fn f(n : ty!{n : i32 | true }) -> ty!{ v : i32 | v > 0 } {
                let mut i = 0 as ty!{i1 : i32 | i1 == 0};
                let mut sum = 0 as ty!{ s : i32 | s == i1*n};
                i = (i + 1) as ty!{a: i32 | a > 0};
                i
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

#[test]
fn test_add_lit() {
    init_tracing();
    with_item_and_rt_lib(
        &quote! {
            fn f(a: ty!{ a : i32 | a > 0 }) -> ty!{ v : i32 | v > 2 } {
                a + 1 + 1
            }
        }
        .to_string(),
        |item, tcx| {
            let ty = type_check_function(item, &tcx).unwrap();
            pretty::assert_eq!(ty.to_string(), "ty!{ v : i32 | v > 2 }");
        },
    )
    .unwrap();
}

#[should_panic]
#[test]
fn test_add_neg() {
    init_tracing();
    with_item_and_rt_lib(
        &quote! {
            fn f(a: ty!{ a : i32 | a < 10 }) -> ty!{ v : i32 | v < 10 } {
                a + 2
            }
        }
        .to_string(),
        |item, tcx| {
            let ty = type_check_function(item, &tcx).unwrap();
            pretty::assert_eq!(ty.to_string(), "ty!{ v : i32 | v > 2 }");
        },
    )
    .unwrap();
}

#[test]
fn test_add_var() {
    init_tracing();
    with_item_and_rt_lib(
        &quote! {
            fn f(a: ty!{ a : i32 | a > 0 }, b: ty!{ b : i32 | b > 0 }) -> ty!{ v : i32 | v > 2 } {
                a + b + b
            }
        }
        .to_string(),
        |item, tcx| {
            let ty = type_check_function(item, &tcx).unwrap();
            pretty::assert_eq!(ty.to_string(), "ty!{ v : i32 | v > 2 }");
        },
    )
    .unwrap();
}

#[should_panic]
#[test]
fn test_add_var_neg() {
    init_tracing();
    with_item_and_rt_lib(
        &quote! {
            fn f(a: ty!{ a : i32 | a < 10 }, b: ty!{ b : i32 | b > 0 }) -> ty!{ v : i32 | v > 2 } {
                a + b + b
            }
        }
        .to_string(),
        |item, tcx| {
            let ty = type_check_function(item, &tcx).unwrap();
            pretty::assert_eq!(ty.to_string(), "ty!{ v : i32 | v > 2 }");
        },
    )
    .unwrap();
}

/// Loops
///
mod loops {
    use super::*;
    #[test]
    fn test_loop_simple() {
        init_tracing();
        with_item_and_rt_lib(
            &quote! {
                fn f() -> ty!{ v : i32 | v > 0 } {
                    let mut res = 1;
                    res as ty!{ s : i32 | s > 0 };
                    while res < 10 {
                        res = (res + 1) as ty!{ a : i32 | a > 0 };
                        ()
                    }
                    res
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
    #[test]
    fn test_loop_neg_trans() {
        init_tracing();
        with_item_and_rt_lib(
            &quote! {
                fn f() -> ty!{v : i32 | v > 0} {
                    let mut res = 1;
                    res as ty!{ s: i32 | s > 0};
                    while res < 10 {
                        res = 0-1;
                        ()
                    }
                    res
                }
            }
            .to_string(),
            |item, tcx| {
                let ty = type_check_function(item, &tcx).unwrap();
            },
        )
        .unwrap();
    }
    #[test]
    fn test_loop_complex() {
        init_tracing();
        with_item_and_rt_lib(
            &quote! {
                fn bad_square(n: ty!{ nv : i32 | nv > 0 }) -> ty!{ v : i32 | v == n * n } {
                    let mut i = 0 as ty!{ iv : i32 | iv == 0};
                    let mut sum = 0 as ty!{ sv : i32 | sv == iv * nv };
                    i = i as ty!{iv2: i32 | iv2 <= nv};
                    while i < n {
                        // Gamma! = {
                            // i : {i1 | true} => {i2 | i2 == i1 + 1}
                            // sum : {s1 | i1 * nv} => {s2 | s2 == i2 * nv}
                        //}
                        i = (i + 1) as ty!{ asd: i32 | asd == iv + 1 };
                        sum = (sum + n) as ty!{ s2 : i32 | s2 == iv * nv };
                        ()
                    }
                    sum
                }

                fn asd() -> ty!{v:i32 | v > 10} {
                    let mut i = 0 as ty!{i1: i32 | i1 == 0};
                    i = (i + 1) as ty!{i2: i32 | i2 == i1 + 1};
                    i
                }
            }
            .to_string(),
            |item, tcx| {
                let ty = type_check_function(item, &tcx).unwrap();
                pretty::assert_eq!(ty.to_string(), "ty!{ v : i32 | v >= n }");
            },
        )
        .unwrap();
    }


    #[test]
    fn test_loop_ssa_complex() {
        init_tracing();
        with_item_and_rt_lib(
            &quote! {
                fn step(
                    n: ty!{ nv : i32 | nv > 0 },
                    i: &mut ty!{i0 : i32 | i0 < nv  => i1 | i1 <= nv},
                    sum: &mut ty!{s0: i32 | s0 == nv * i0 => s1 | s1 == nv * i1 && s1 == 1337}
                ) -> ty!{ v: i32 } {
                    let i0 = *i as ty!{i00 : i32 | i00 < nv };
                    *i = (i0 + 1) as ty!{i2: i32 | i2 == i00 + 1};
                    let s0 = *sum as ty!{s00 : i32 | s00 == nv * i00};
                    // *sum = s0 + n;
                    0
                }
                // fn bad_square(n: ty!{ nv : i32 | nv > 0 }) -> ty!{ v : i32 | v == nv * nv } {
                //     let mut i = 0 as ty!{ iv : i32 | iv == 0};
                //     let mut sum = 0 as ty!{ sv : i32 | sv == 0 };
                //     sum = sum as ty!{ sv2 : i32 |  sv2 == nv * iv};
                //     i = i as ty!{iv2: i32 | iv2 <= nv};
                //     while i < n {
                //         // Inv: i <= nv && sum == n * i
                //         let j = i as ty!{i_old: i32 | i_old < nv && sv == i_old * nv};
                        
                //         // sum = (sum + n) as ty!{s: i32 | s == (i_old + 1) * nv };
                //         i = (j + 1) as ty!{i_new : i32 | i_new == i_old + 1 };
                //         ()
                //     }
                //     sum
                // }
            }
            .to_string(),
            |item, tcx| {
                let ty = type_check_function(item, &tcx).unwrap();
                pretty::assert_eq!(ty.to_string(), "ty!{ v : i32 | v >= n }");
            },
        )
        .unwrap();
    }

    #[test]
    fn test_loop_keep_predicates_complex() {
        init_tracing();
        with_item_and_rt_lib(
            &quote! {
                fn bad_square(n: ty!{ nv : i32 | nv > 0 }) -> ty!{ v : i32 | v == n * n } {
                    let mut i = 0 as ty!{ iv : i32 | iv == 0};
                    let mut sum = 0 as ty!{ sv : i32 | sv == 0 };
                    i = i as ty!{iv2: i32 | iv2 <= nv};
                    while i < n {
                        i = i as ty!{iold: i32 | iold <= nv};
                        sum = sum as ty!{sumold: i32 | sumold == iold*nv};

                        i = i+1 as ty!{i2: i32 | i2 == iold+1};
                        sum = sum+n as ty!{sum2: i32 | sum2 == sumold+nv};

                        i = i as ty!{inew: i32 | inew <= nv};
                        sum = sum as ty!{sumnew: i32 | sumnew == inew*nv};
                        ()
                    }
                    sum
                }
            }
            .to_string(),
            |item, tcx| {
                let ty = type_check_function(item, &tcx).unwrap();
                pretty::assert_eq!(ty.to_string(), "ty!{ v : i32 | v >= n }");
            },
        )
        .unwrap();
    }

    #[test]
    fn test_loop_simple_invariant() {
        init_tracing();
        with_item_and_rt_lib(
            &quote! {
                fn f(n: ty!{nv: i32 | nv > 0}) -> ty!{r: i32 | r == nv} {
                    let mut i = 0 as ty!{iv : i32 | iv==0};
                    i = i as ty!{iv2 : i32 | iv2 <= nv}; // Invariant
                    while i < n {
                        let j = i as ty!{jv : i32 | jv < nv};
                        i = (j + 1) as ty!{iv2 : i32 | iv2 <= nv};
                        
                        ()
                    }
                    i
                }
            }
            .to_string(),
            |item, tcx| {
                let ty = type_check_function(item, &tcx).unwrap();
                pretty::assert_eq!(ty.to_string(), "ty!{ r : i32 | r == nv }");
            },
        )
        .unwrap();
    }

}

/// Mutable Type Annotations
///
mod mut_ty_annotation {
    use super::*;
    #[test]
    fn test_mut_ann_pos() {
        init_tracing();
        with_item_and_rt_lib(
            &quote! {
                fn bad_square(n: &mut ty!{ nv : i32 | true => na | na > 0 }) -> ty!{ v : i32 | true } {
                    *n = 2;
                    0
                }
            }
            .to_string(),
            |item, tcx| {
                let ty = type_check_function(item, &tcx).unwrap();
                pretty::assert_eq!(ty.to_string(), "ty!{ v : i32 | true }");
            },
        )
        .unwrap();
    }

    #[should_panic]
    #[test]
    fn test_mut_ann_neg() {
        init_tracing();
        with_item_and_rt_lib(
            &quote! {
                fn bad_square(n: &mut ty!{ nv : i32 | true => na | na > 0 }) -> ty!{ v : i32 | true } {
                    *n = 0;
                    0
                }
            }
            .to_string(),
            |item, tcx| {
                let ty = type_check_function(item, &tcx).unwrap();
                pretty::assert_eq!(ty.to_string(), "ty!{ v : i32 | true }");
            },
        )
        .unwrap();
    }
}
