#![feature(rustc_private)]
#![feature(box_patterns)]

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

use constraint_generator::type_check_function;
use rustc_driver::Compilation;

use rustc_hir as hir;

use rustc_interface::interface;

use rustc_interface::Queries;
use tracing::error;
use tracing_subscriber::EnvFilter;

use std::str;

use tracing::info_span;
use tracing::trace;

use crate::constraint_generator::ErrorSpan;
use crate::constraint_generator::RefinementError;

mod hir_ext;

mod buildin_functions;
mod constraint_generator;
mod refinement_context;
mod refinements;
mod smtlib_ext;
#[cfg(test)]
mod test_with_rustc;

struct MyLint;

impl rustc_lint::LintPass for MyLint {
    fn name(&self) -> &'static str {
        "The best lint"
    }
}

impl<'tcx> rustc_lint::LateLintPass<'tcx> for MyLint {
    fn check_expr(&mut self, _cx: &rustc_lint::LateContext<'tcx>, _expr: &rustc_hir::Expr<'tcx>) {
        // Static analysis goes here
    }

    fn check_fn(
        &mut self,
        late: &rustc_lint::LateContext<'tcx>,
        _: rustc_hir::intravisit::FnKind<'tcx>,
        _: &'tcx rustc_hir::FnDecl<'tcx>,
        _: &'tcx rustc_hir::Body<'tcx>,
        _: rustc_span::Span,
        hir_id: rustc_hir::HirId,
    ) {
        let hir_node = late.tcx.hir().get(hir_id);
        println!("{:?}", hir_node)
    }
}

struct OurCompilerCalls {}
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
            let _def_ids_with_body: Vec<_> = tcx
                .mir_keys(())
                .iter()
                .flat_map(|&local_def_id| {
                    // Skip items that are not functions or methods.

                    let hir_id = tcx.hir().local_def_id_to_hir_id(local_def_id);
                    let hir_node = tcx.hir().get(hir_id);
                    match hir_node {
                        hir::Node::Item(
                            fn_item @ hir::Item {
                                kind: hir::ItemKind::Fn(_, _, _),
                                span,
                                ..
                            },
                        ) => {
                            let _res = type_check_function(fn_item, &tcx);
                            match _res {
                                Ok(_) => (),
                                Err(e) => {
                                    error!("{}", e);
                                    if fn_item.ident.to_string() == "main" {
                                        // skip error
                                        // IDE some how creates empty main that causes problems
                                        // FIXME: skip this
                                    } else {
                                        let specific_span = match e.downcast_ref::<ErrorSpan>() {
                                            Some(span) => span.location,
                                            None => *span,
                                        };
                                        match e.downcast_ref::<RefinementError>() {
                                            Some(r) => {
                                                error!("specific error, {:?}", e);
                                                let mut err = session
                                                    .struct_span_err(specific_span, &r.message);
                                                if let Some(ce) = &r.counter_example {
                                                    err.span_help(
                                                        specific_span,
                                                        &format!("Counter-Example: {}", ce),
                                                    );
                                                }
                                                err.emit();
                                            }
                                            None => {
                                                error!("generic error");
                                                // see: https://rustc-dev-guide.rust-lang.org/diagnostics.html?highlight=diagnost#error-messages
                                                let mut err = session.struct_span_err(
                                                    specific_span,
                                                    &format!("{:?}", e),
                                                );
                                                err.emit();
                                            }
                                        }
                                    }
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

    trace!("rustc arguments: {:?}", compiler_args);

    let mut callbacks = OurCompilerCalls {};
    // Invoke compiler, and handle return code.
    let exit_code = rustc_driver::catch_with_exit_code(move || {
        rustc_driver::RunCompiler::new(&compiler_args, &mut callbacks).run()
    });
    std::process::exit(exit_code)
}

fn main() {
    let file_appender = tracing_appender::rolling::never("/tmp/corten", "debug.log");
    tracing_subscriber::fmt::fmt()
        .with_env_filter(EnvFilter::from_env("CORTEN_LOG"))
        .with_writer(file_appender)
        .pretty()
        .init();
    prusti_main();
}
