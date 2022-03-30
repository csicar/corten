#![feature(rustc_private)]

// NOTE: For the example to compile, you will need to first run the following:
//     rustup component add rustc-dev llvm-tools-preview

// version: 1.53.0-nightly (9b0edb7fd 2021-03-27)

extern crate rustc_ast_pretty;
extern crate rustc_driver;
extern crate rustc_ast;
extern crate rustc_error_codes;
extern crate rustc_errors;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_interface;
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
use rustc_session::config;
use rustc_span::source_map;
use tracing::error;
use tracing::info;
use tracing::trace;
use tracing::info_span;
use std::path;
use std::process;
use std::str;

mod hir_ext;
use hir_ext::GenericArgExt;
use crate::hir_ext::TyExt;

struct OurCompilerCalls {
    args: Vec<String>,
}
impl rustc_driver::Callbacks for OurCompilerCalls {


    fn after_parsing<'tcx>(&mut self, compiler: &interface::Compiler, queries: &'tcx Queries<'tcx>) -> Compilation {
        let _span = info_span!("after_parsing").entered();
        let krate= &mut *queries.parse().unwrap().peek_mut();
        
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
        queries.global_ctxt().unwrap().take().enter(|tcx| {
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
                            kind: hir::ItemKind::Fn(FnSig {decl: FnDecl {output, ..}, ..}, ..),
                            ident,
                            ..
                        })
                          => {
                            
                            // // search for specification
                            // let expected_name = "refinement_spec_for_".to_owned() + ident.name.as_str(); 
                            // let spec = tcx.mir_keys(()).iter().map(|id| tcx.hir().get_by_def_id(*id)).find_map(|node| {
                            //     if let hir::Node::Item(hir::Item { ident, kind: hir::ItemKind::Const(_ty, body_id), ..}) =  node {
                            //         if ident.name.as_str() == expected_name {
                            //             Some(body_id)
                            //         } else {
                            //             None
                            //         }
                            //     } else {
                            //         None
                            //     }
                            //  }).and_then(|body_id| {
                            //      let body = tcx.hir().get(body_id.hir_id);
                            //      if let hir::Node::Expr(
                            //          hir::Expr { kind: hir::ExprKind::Lit(source_map::Spanned { node: rustc_ast::LitKind::Str(symbol, _), .. }), ..}) = body {
                            //         let json_text = symbol.as_str();
                            //         let syn_tree = syn_serde::json::from_str::<syn::Type>(json_text).expect("Error deserializing specification");
                            //         Some(syn_tree)
                            //      } else {
                            //          None
                            //      }
                            //  });
                            //  info!("found spec {:?}", spec);
                            match output {
                                hir::FnRetTy::Return(return_type) => {
                                    let refinement = return_type.try_into_refinement(&tcx);
                                    info!(?refinement, "found refinement");
                                },
                                o => {
                                    error!("unrefined function: {:?}", o)
                                }
                            }

                              Some((local_def_id, hir_node))
                            
                            },
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

struct RefinementType<'t> {
    ty: Ty<'t>,
    refinement: Expr<'t>
}

fn parse_refinement_type() {

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

    compiler_args.push("-Zpolonius".to_owned());
    compiler_args.push("-Zalways-encode-mir".to_owned());
    compiler_args.push("-Zcrate-attr=feature(register_tool)".to_owned());

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
        .pretty().init();
    prusti_main();
}



fn other_main() {
    let out = process::Command::new("rustc")
        .arg("--print=sysroot")
        .current_dir(".")
        .output()
        .unwrap();
    let sysroot = str::from_utf8(&out.stdout).unwrap().trim();
    let config = rustc_interface::Config {
        opts: config::Options {
            maybe_sysroot: Some(path::PathBuf::from(sysroot)),
            ..config::Options::default()
        },
        input: config::Input::Str {
            name: source_map::FileName::Custom("main.rs".to_string()),
            input: include_str!("../examples/macro.rs")
                // "fn main() { let message = \"Hello, world!\".to_string(); println!(\"{}\", message); }"
                .to_string(),
        },
        diagnostic_output: rustc_session::DiagnosticOutput::Default,
        crate_cfg: rustc_hash::FxHashSet::default(),
        input_path: None,
        output_dir: None,
        output_file: None,
        file_loader: None,
        lint_caps: rustc_hash::FxHashMap::default(),
        parse_sess_created: None,
        register_lints: None,
        override_queries: None,
        make_codegen_backend: None,
        registry: registry::Registry::new(&rustc_error_codes::DIAGNOSTICS),
    };
    rustc_interface::run_compiler(config, |compiler| {
        compiler.enter(|queries| {
            // TODO: add this to -Z unpretty
            let ast_krate = queries.parse().unwrap().take();
            for item in ast_krate.items {
                println!("{}", item_to_string(&item));
            }
  
            // Analyze the crate and inspect the types under the cursor.
            queries.global_ctxt().unwrap().take().enter(|tcx| {
                // Every compilation contains a single crate.
                let hir_krate = tcx.hir();
                // Iterate over the top-level items in the crate, looking for the main function.
                for item in hir_krate.items() {
                    // Use pattern-matching to find a specific node inside the main function.
                    if let rustc_hir::ItemKind::Fn(_, _, body_id) = item.kind {
                        let expr = &tcx.hir().body(body_id).value;
                        if let rustc_hir::ExprKind::Block(block, _) = expr.kind {
                            if let rustc_hir::StmtKind::Local(local) = block.stmts[0].kind {
                                if let Some(expr) = local.init {
                                    let hir_id = expr.hir_id; // hir_id identifies the string "Hello, world!"
                                    let def_id = tcx.hir().local_def_id(item.hir_id()); // def_id identifies the main function
                                    let ty = tcx.typeck(def_id).node_type(hir_id);
                                    println!("{:?}: {:?}", expr, ty); // prints expr(HirId { owner: DefIndex(3), local_id: 4 }: "Hello, world!"): &'static str
                                }
                            }
                        }
                    }
                }
            })
        });
    });
  }
  