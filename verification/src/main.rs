#![feature(rustc_private)]

// NOTE: For the example to compile, you will need to first run the following:
//     rustup component add rustc-dev llvm-tools-preview

// version: 1.53.0-nightly (9b0edb7fd 2021-03-27)

extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_driver;
extern crate rustc_error_codes;
extern crate rustc_errors;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_hir_pretty;
extern crate rustc_interface;
extern crate rustc_lint;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

use rustc_ast_pretty::pprust::item_to_string;
use rustc_driver::Compilation;
use rustc_errors::registry;
use rustc_hir as hir;
use rustc_hir::Expr;
use rustc_hir::FnDecl;
use rustc_hir::FnSig;
use rustc_hir::Ty;
use rustc_interface::interface;
use rustc_interface::Config;
use rustc_interface::Queries;
use rustc_middle::ty::TyCtxt;
use rustc_middle::ty::WithOptConstParam;
use rustc_session::config;
use rustc_span::source_map;
use std::path;
use std::process;
use std::str;
use tracing::error;
use tracing::info;
use tracing::info_span;
use tracing::trace;

mod hir_ext;
use crate::hir_ext::TyExt;
use hir_ext::GenericArgExt;
mod constraint_generator;
mod refinements;
#[cfg(test)]
mod test_with_rustc;

struct MyLint;

impl rustc_lint::LintPass for MyLint {
    fn name(&self) -> &'static str {
        "The best lint"
    }
}

impl<'tcx> rustc_lint::LateLintPass<'tcx> for MyLint {
    fn check_expr(&mut self, cx: &rustc_lint::LateContext<'tcx>, expr: &rustc_hir::Expr<'tcx>) {
        // Static analysis goes here
    }
}

struct OurCompilerCalls {
    args: Vec<String>,
}
impl rustc_driver::Callbacks for OurCompilerCalls {
    fn after_parsing<'tcx>(
        &mut self,
        compiler: &interface::Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        let _span = info_span!("after_parsing").entered();
        let krate = &mut *queries.parse().unwrap().peek_mut();

        // a.enter(|tx| {});
        rustc_driver::pretty::print_after_parsing(
            compiler.session(),
            compiler.input(),
            krate,
            rustc_session::config::PpMode::Source(rustc_session::config::PpSourceMode::Normal),
            None,
        );

        krate.items.iter().for_each(|item| {
            trace!("Item: {}, {:?}", item.id, item);
        });
        Compilation::Continue
    }

    fn after_analysis<'tcx>(
        &mut self,
        compiler: &interface::Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        let _span = info_span!("after_analysis").entered();

        let session = compiler.session();
        session.abort_if_errors();

        // Analyze the crate and inspect the types under the cursor.
        queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            // Every compilation contains a single crate.
            let mut def_ids_with_body: Vec<_> = tcx
                .mir_keys(())
                .iter()
                .flat_map(|&local_def_id| {
                    // Skip items that are not functions or methods.
                    let hir_id = tcx.hir().local_def_id_to_hir_id(local_def_id);
                    let hir_node = tcx.hir().get(hir_id);
                    match hir_node {
                        hir::Node::Item(hir::Item {
                            kind:
                                hir::ItemKind::Fn(
                                    FnSig {
                                        decl: FnDecl { output, .. },
                                        ..
                                    },
                                    _,
                                    body_id,
                                ),
                            ident,
                            def_id,
                            ..
                        }) => {
                            let body = tcx.hir().get(body_id.hir_id);
                            trace!(?body_id, ?body, "function");
                            let hir_id = body_id.hir_id;
                            let local_ctx = tcx.typeck(*def_id);

                            let ctx = vec![];
                            let ty =
                                constraint_generator::type_of_node(&body, &tcx, local_ctx, &ctx);
                            trace!(?ty, "body type");

                            match output {
                                hir::FnRetTy::Return(return_type) => {
                                    let refinement =
                                        refinements::extract_refinement_from_type_alias(
                                            return_type,
                                            &tcx,
                                            local_ctx,
                                        )
                                        .expect("error extracting a refinement from a type alias");
                                    info!(?refinement, "found refinement");
                                    // let constr =
                                    //     constraint_generator::type_check_node(&body, &tcx, todo!());
                                    // info!("constraints: {:#?}", constr);
                                }
                                o => {
                                    error!("unrefined function: {:?}", o)
                                }
                            }

                            Some("")
                        }
                        _ => None,
                    }
                })
                .collect();
            // def_ids_with_body.iter().for_each(|(id, def)| {
            //     trace!("Item {:?} {:?}", id, def);
            // });
        });

        Compilation::Continue
    }
}

// see: https://github.com/viperproject/prusti-dev/blob/1a7ac32128ca2a63ce05944369a7f13b0674a1f8/analysis/src/bin/gen-accessibility-driver.rs
fn prusti_main() {
    rustc_driver::init_rustc_env_logger();
    let mut compiler_args = Vec::new();
    let mut callback_args = Vec::new();
    for arg in std::env::args() {
        if arg.starts_with("--generate-test-program") {
            callback_args.push(arg);
        } else {
            compiler_args.push(arg);
        }
    }

    compiler_args.push("-Zalways-encode-mir".to_owned());

    let mut callbacks = OurCompilerCalls {
        args: callback_args,
    };
    // Invoke compiler, and handle return code.
    let exit_code = rustc_driver::catch_with_exit_code(move || {
        rustc_driver::RunCompiler::new(&compiler_args, &mut callbacks).run()
    });
    std::process::exit(exit_code)
}

fn main() {
    tracing_subscriber::fmt::fmt()
        .with_env_filter(tracing_subscriber::EnvFilter::new("trace"))
        .pretty()
        .init();
    prusti_main();
}