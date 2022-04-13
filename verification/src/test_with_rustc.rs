use rustc_driver::Compilation;

use rustc_errors::ErrorReported;
use rustc_hir as hir;

use rustc_hir::FnDecl;
use rustc_hir::FnSig;
use rustc_interface::interface;
use rustc_interface::Config;
use rustc_interface::Queries;
use rustc_middle::ty::TyCtxt;

use rustc_middle::ty::TypeckResults;
use rustc_session::config;
use rustc_span::source_map;
use tracing::warn;
use std::path;
use std::process;
use std::str;
use std::sync::RwLock;
use tracing::error;

use quote::quote;

struct HirCallback<F: Send> {
    with_hir: RwLock<F>,
    input: String,
    sys_root: Option<path::PathBuf>,
}

impl<F: for<'a> FnMut(hir::Node<'a>, TyCtxt<'a>) -> () + Send> rustc_driver::Callbacks
    for HirCallback<F>
{
    fn config(&mut self, config: &mut Config) {
        config.input = config::Input::Str {
            name: source_map::FileName::Custom("file_under_test_name.rs".to_string()),
            input: self.input.clone(),
        };
        config.output_dir = Some(path::PathBuf::from("/tmp/test-rustc"));
        config.opts.maybe_sysroot = self.sys_root.clone();
        config.make_codegen_backend = None;
    }

    fn after_analysis<'tcx>(
        &mut self,
        compiler: &interface::Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        let session = compiler.session();
        session.abort_if_errors();

        queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            tcx.mir_keys(()).iter().for_each(|&local_def_id| {
                // Skip items that are not functions or methods.
                let hir_id = tcx.hir().local_def_id_to_hir_id(local_def_id);
                let hir_node = tcx.hir().get(hir_id);
                let mut callback = self.with_hir.write().unwrap();
                (callback)(hir_node, tcx);
            });
        });

        Compilation::Continue
    }
}

pub fn with_hir<F>(callback: F, input: &str) -> Result<(), ErrorReported>
where
    F: for<'a> FnMut(hir::Node<'a>, TyCtxt<'a>) -> () + Send,
{
    let out = process::Command::new("rustc")
        .arg("--print=sysroot")
        .current_dir(".")
        .output()
        .unwrap();
    let sysroot = str::from_utf8(&out.stdout).unwrap().trim();
    let cb = RwLock::new(callback);
    let header = quote! {
        #![feature(adt_const_params)]
        #![allow(dead_code)]
        #![allow(incomplete_features)]

    };

    let mut callback = HirCallback {
        with_hir: cb,
        input: header.to_string() + "\n// --- test input --- //\n\n" + input,
        sys_root: Some(path::PathBuf::from(sysroot)),
    };
    let args: Vec<String> = vec![
        "-v".into(),
        "--crate-type".into(),
        "lib".into(),
        "/tmp/a".into(), // this input gets overridden by the Callback, but the rustc cli parser still requires *some* file as input
    ];
    rustc_driver::RunCompiler::new(&args, &mut callback).run()
}

pub fn with_item<F>(input: &str, mut callback: F) -> Result<(), ErrorReported>
where
    F: for<'a> FnMut(&hir::Item<'a>, TyCtxt<'a>) -> () + Send,
{
    with_hir(
        |hir, tcx| match hir {
            hir::Node::Item(item) => callback(item, tcx),
            o => warn!(node=?o, "parsing input resulted in different stuff"),
        },
        input,
    )
}

pub fn with_expr<F>(input: &str, mut callback: F) -> Result<(), ErrorReported>
where
    F: for<'a> FnMut(&hir::Expr<'a>, TyCtxt<'a>, &TypeckResults<'a>) -> () + Send,
{
    with_item(input, |item, tcx| match &item.kind {
        hir::ItemKind::Fn(
            FnSig {
                decl: FnDecl { output: _, .. },
                ..
            },
            _,
            body_id,
        ) => {
            let hir = (tcx as TyCtxt).hir();
            let node = hir.get(body_id.hir_id);
            let local_ctx = tcx.typeck(item.def_id);

            match node {
                hir::Node::Expr(expr) => callback(expr, tcx, local_ctx),
                _o => todo!(),
            }
        }
        _o => panic!("parsing input resulted in different stuff"),
    })
}

#[test_log::test]
fn test_item() {
    with_item("fn main() {}", |item, _tcx| println!("{:?}", item)).unwrap();
}
