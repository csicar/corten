use std::fmt::Display;

use petgraph::{graph::NodeIndex, Graph};
use rustc_hir::{
    intravisit::{walk_block, walk_expr, walk_stmt, Visitor},
    Block, Expr, HirId, Local,
};
use rustc_hir_pretty::id_to_string;
use rustc_middle::ty::TyCtxt;
use tracing::trace;

use crate::hir_ext::ExprExt;

#[derive(Debug)]
struct Entry {
    hir_id: HirId,
    code: String,
}

impl Entry {
    fn new<'hir>(hir_id: HirId, tcx: &TyCtxt<'hir>) -> Self {
        let code = id_to_string(&tcx.hir(), hir_id);
        Entry { hir_id, code }
    }
}

struct BasicBlock {
    entries: Vec<Entry>,
}

struct CfgVisitor<'tcx, 'a> {
    cfg: Graph<Entry, ()>,
    current_pred: NodeIndex,
    tcx: &'a TyCtxt<'tcx>,
}

impl<'a, 'v, 'tcx> Visitor<'v> for CfgVisitor<'tcx, 'a> {
    type NestedFilter = rustc_middle::hir::nested_filter::All;
    fn visit_expr(&mut self, ex: &'v Expr<'v>) {
        match ex.kind {
            rustc_hir::ExprKind::Let(_) => todo!(),
            rustc_hir::ExprKind::If(cond, then_expr, else_expr) => {
                walk_expr(self, cond);

                let cond_idx = self.current_pred;

                walk_expr(self, then_expr);
                let then_exit = self.current_pred;

                self.current_pred = cond_idx;
                else_expr.map(|e| walk_expr(self, e));
                let else_exit = self.current_pred;

                let whole_idx = self.cfg.add_node(Entry::new(ex.hir_id, &self.tcx));
                self.cfg.add_edge(then_exit, whole_idx, ());
                self.cfg.add_edge(else_exit, whole_idx, ());
                self.current_pred = whole_idx;
            }
            rustc_hir::ExprKind::Loop(block, _, _, _) => {
                // Loop has two targets:
                // 1. the loop entry point (designated block.hir_id)
                // 2. the loop exit point (designated ex.hir_id, because that is where break.target_id points to)
                let entry_idx = self.cfg.add_node(Entry::new(block.hir_id, &self.tcx));
                let exit_idx = self.cfg.add_node(Entry::new(ex.hir_id, &self.tcx));

                let while_pred = self.current_pred;

                trace!(entry_id=?block.hir_id, exit_id=?ex.hir_id);
                self.cfg.add_edge(while_pred, entry_idx, ());
                
                // self.cfg.add_edge(entry_idx, exit_idx, ());
                // self.cfg.add_edge(entry_idx, entry_idx, ());
                // self.cfg.add_edge(exit_idx, exit_idx, ());

                self.current_pred = entry_idx;

                walk_block(self, block);

                self.cfg.add_edge(self.current_pred, entry_idx, ());

                self.current_pred = exit_idx;
            }
            rustc_hir::ExprKind::Break(destination, value) => {
                if value.is_some() {
                    todo!()
                }
                let idx = self.cfg.add_node(Entry::new(ex.hir_id, &self.tcx));
                let dest_hir_id = destination.target_id.unwrap();
                let dest_idx = self
                    .cfg
                    .node_indices()
                    .filter(|idx| {
                        let entry = &self.cfg[*idx];
                        entry.hir_id == dest_hir_id
                    })
                    .collect::<Vec<NodeIndex>>();
                trace!(?dest_idx, ?dest_hir_id, ?idx, hir_id = ?ex.hir_id, "break references");

                self.cfg.add_edge(idx, dest_idx[0], ());
            }
            rustc_hir::ExprKind::Err => todo!(),
            _ => {
                walk_expr(self, ex);
                let idx = self.cfg.add_node(Entry::new(ex.hir_id, &self.tcx));
                self.cfg.add_edge(self.current_pred, idx, ());
                self.current_pred = idx;
            }
        }
    }

    fn visit_stmt(&mut self, s: &'v rustc_hir::Stmt<'v>) {
        trace!(stmt=?s.hir_id,"visit stmt");
        walk_stmt(self, s);
        let idx = self.cfg.add_node(Entry::new(s.hir_id, &self.tcx));
        self.cfg.add_edge(self.current_pred, idx, ());
        self.current_pred = idx;
    }
}

fn calculate_cfg<'a, 'tcx, 'hir>(tcx: &TyCtxt<'hir>, start: &'a Expr<'tcx>) -> Graph<Entry, ()>
// TODO: replace HirId with BasicBlock?
where
    'tcx: 'hir,
{
    let mut cfg: Graph<Entry, ()> = Graph::new();
    let current_pred = cfg.add_node(Entry::new(start.hir_id, &tcx));
    let mut visitor = CfgVisitor {
        cfg: Graph::new(),
        current_pred,
        tcx: &tcx,
    };
    walk_expr(&mut visitor, start);
    visitor.cfg
}

#[cfg(test)]
mod test {
    use std::io::Write;
    use std::process::Command;
    use std::{fs::File, path::Path};

    use petgraph::dot::{Config, Dot};
    use pretty_assertions as pretty;
    use quote::quote;
    use tracing::info;

    use super::*;
    use crate::test_with_rustc::with_expr;

    fn write_dot_file(file_name: &str, content: &str) {
        let dot_file_path = Path::new(file_name);
        let mut dot_file = File::create(dot_file_path).unwrap();
        write!(dot_file, "{}", content).unwrap();

        Command::new("dot")
            .args(["-T", "svg", dot_file_path.to_str().unwrap(), "-O"])
            .output()
            .unwrap();

        info!("wrote dot file to: file://{}", dot_file_path.display());
    }

    #[test_log::test]
    fn test_cfg_if() {
        with_expr(
            &quote! {
              fn test() {
                let mut a = 1;
                let mut b = 4;
                a = 3;
                if a > 3 {
                  b = 3;
                } else {
                  b = 4;
                }
                a = 9;
              }
            }
            .to_string(),
            |expr, tcx, local_ctx| {
                let graph = calculate_cfg(&tcx, expr);
                let only_code = graph.map(|_, node| node.code.clone(), |_, e| "");

                let actual_dot = format!(
                    "{}",
                    Dot::with_config(
                        &only_code,
                        &[Config::EdgeNoLabel]
                    )
                );
                let actual_dot_full = format!(
                  "{:#?}",
                  Dot::with_attr_getters(
                      &graph,
                      &[Config::EdgeNoLabel],
                      &|_, _| "".to_string(),
                      &|_, _| ", shape=rounded".to_string(),
                  )
              );
                write_dot_file("/tmp/graph-test_cfg_if.dot", &actual_dot_full);

                let expected = r#"
                  digraph {
                      0 [ label = "1" ]
                      1 [ label = "let mut a = 1;" ]
                      2 [ label = "4" ]
                      3 [ label = "let mut b = 4;" ]
                      4 [ label = "3" ]
                      5 [ label = "a" ]
                      6 [ label = "a = 3" ]
                      7 [ label = "a = 3;" ]
                      8 [ label = "a" ]
                      9 [ label = "3" ]
                      10 [ label = "a > 3" ]
                      11 [ label = "3" ]
                      12 [ label = "b" ]
                      13 [ label = "b = 3" ]
                      14 [ label = "b = 3;" ]
                      15 [ label = "4" ]
                      16 [ label = "b" ]
                      17 [ label = "b = 4" ]
                      18 [ label = "b = 4;" ]
                      19 [ label = "" ]
                      20 [ label = "" ]
                      21 [ label = "9" ]
                      22 [ label = "a" ]
                      23 [ label = "a = 9" ]
                      24 [ label = "a = 9;" ]
                      0 -> 0 [ ]
                      0 -> 1 [ ]
                      1 -> 2 [ ]
                      2 -> 3 [ ]
                      3 -> 4 [ ]
                      4 -> 5 [ ]
                      5 -> 6 [ ]
                      6 -> 7 [ ]
                      7 -> 8 [ ]
                      8 -> 9 [ ]
                      9 -> 10 [ ]
                      10 -> 11 [ ]
                      11 -> 12 [ ]
                      12 -> 13 [ ]
                      13 -> 14 [ ]
                      10 -> 15 [ ]
                      15 -> 16 [ ]
                      16 -> 17 [ ]
                      17 -> 18 [ ]
                      14 -> 19 [ ]
                      18 -> 19 [ ]
                      19 -> 20 [ ]
                      20 -> 21 [ ]
                      21 -> 22 [ ]
                      22 -> 23 [ ]
                      23 -> 24 [ ]
                  }"#
                .trim();
                pretty::assert_eq!(
                    actual_dot.trim(),
                    expected.replace("                  ", "")
                );
            },
        )
        .unwrap();
    }

    #[test_log::test]
    fn test_cfg_while() {
        with_expr(
            &quote! {
              fn test() {
                let mut a = 1;
                let mut b = 4;
                a = 3;
                while a > 3 {
                  b = 3;
                }
                a = 9;
              }
            }
            .to_string(),
            |expr, tcx, _local_ctx| {
                let graph = calculate_cfg(&tcx, expr);
                let only_code = graph.map(|_, node| node.code.clone(), |_, _| "");

                let vis_graph = graph.map(|_, node| format!("{{ {} }} | {{ lid {:?} }}", node.code, node.hir_id.local_id), |_, _| "");
                let actual_dot = format!(
                    "{}",
                    Dot::with_config(
                        &only_code,
                        &[Config::EdgeNoLabel],
                    )
                );
                let actual_dot_full = format!(
                    "{}",
                    Dot::with_attr_getters(
                        &vis_graph,
                        &[Config::EdgeNoLabel],
                        &|_, _| "".to_string(),
                        &|_, _| ", shape=record".to_string(),
                    )
                );
                write_dot_file("/tmp/graph-test_cfg_while.dot", &actual_dot_full);

                let expected = r#"
                  digraph {
                      0 [ label = "1" ]
                      1 [ label = "let mut a = 1;" ]
                      2 [ label = "4" ]
                      3 [ label = "let mut b = 4;" ]
                      4 [ label = "3" ]
                      5 [ label = "a" ]
                      6 [ label = "a = 3" ]
                      7 [ label = "a = 3;" ]
                      8 [ label = "a" ]
                      9 [ label = "3" ]
                      10 [ label = "a > 3" ]
                      11 [ label = "3" ]
                      12 [ label = "b" ]
                      13 [ label = "b = 3" ]
                      14 [ label = "b = 3;" ]
                      15 [ label = "4" ]
                      16 [ label = "b" ]
                      17 [ label = "b = 4" ]
                      18 [ label = "b = 4;" ]
                      19 [ label = "" ]
                      20 [ label = "" ]
                      21 [ label = "9" ]
                      22 [ label = "a" ]
                      23 [ label = "a = 9" ]
                      24 [ label = "a = 9;" ]
                      0 -> 0 [ ]
                      0 -> 1 [ ]
                      1 -> 2 [ ]
                      2 -> 3 [ ]
                      3 -> 4 [ ]
                      4 -> 5 [ ]
                      5 -> 6 [ ]
                      6 -> 7 [ ]
                      7 -> 8 [ ]
                      8 -> 9 [ ]
                      9 -> 10 [ ]
                      10 -> 11 [ ]
                      11 -> 12 [ ]
                      12 -> 13 [ ]
                      13 -> 14 [ ]
                      10 -> 15 [ ]
                      15 -> 16 [ ]
                      16 -> 17 [ ]
                      17 -> 18 [ ]
                      14 -> 19 [ ]
                      18 -> 19 [ ]
                      19 -> 20 [ ]
                      20 -> 21 [ ]
                      21 -> 22 [ ]
                      22 -> 23 [ ]
                      23 -> 24 [ ]
                  }"#
                .trim();
                pretty::assert_eq!(
                    actual_dot.trim(),
                    expected.replace("                  ", "")
                );
            },
        )
        .unwrap();
    }
}
