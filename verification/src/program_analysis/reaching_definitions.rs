//! This module contains functions to perform reachable definition
//! analysis on the HIR
//!
//! ## Example
//!
//! Given:
//! ```rust
//! fn test(a: &mut i32 /* #1 */) {
//!    a /* #2 */ = 3
//!    // Reaching Definitions: #1
//!    
//!    while a < 0 {
//!       a += 1; /* #3 */
//!       // Reaching Definitions: #2, #3
//!    }
//!    a
//!    // Reaching Definitions: #2, #3
//! }
//! ```

use std::collections::{HashMap, HashSet, VecDeque};

use rustc_hir::{Expr, HirId, Block};
use rustc_middle::{hir::map::Map, ty::TyCtxt};

use crate::hir_ext::NodeExt;

fn calculate_reachable_definitions<'tcx, 'hir>(
    tcx: &TyCtxt<'hir>,
    start: &Expr<'tcx>,
) -> HashMap<HirId, HashSet<HirId>>
where
    'tcx: 'hir,
{
    let mut defs = HashMap::new();

    // worklist; adding new items to the front and consuming items at the end
    let mut worklist : VecDeque<HirId> = VecDeque::from([start.hir_id]);

    while let Some(next) = worklist.pop_back() {
      step(tcx, next, &mut worklist, &mut defs);
    }
    defs
}

fn step<'tcx, 'hir>(
  tcx: &TyCtxt<'hir>,
  item_id: HirId,
  worklist:  &mut VecDeque<HirId>,
  reaching_definitions: &mut HashMap<HirId, HashSet<HirId>>
) -> HashMap<HirId, HashSet<HirId>>
where
  'tcx: 'hir,
{
  let node = tcx.hir().get(item_id);
  let expr = node.try_into_expr().unwrap();
  match expr.kind {
    rustc_hir::ExprKind::Box(_) => todo!(),
    rustc_hir::ExprKind::ConstBlock(_) => todo!(),
    rustc_hir::ExprKind::Array(_) => todo!(),
    rustc_hir::ExprKind::Call(_, _) => todo!(),
    rustc_hir::ExprKind::MethodCall(_, _, _) => todo!(),
    rustc_hir::ExprKind::Tup(_) => todo!(),
    rustc_hir::ExprKind::Binary(_, _, _) => todo!(),
    rustc_hir::ExprKind::Unary(_, _) => todo!(),
    rustc_hir::ExprKind::Lit(_) => todo!(),
    rustc_hir::ExprKind::Cast(_, _) => todo!(),
    rustc_hir::ExprKind::Type(_, _) => todo!(),
    rustc_hir::ExprKind::DropTemps(_) => todo!(),
    rustc_hir::ExprKind::Let(_) => todo!(),
    rustc_hir::ExprKind::If(_, _, _) => todo!(),
    rustc_hir::ExprKind::Loop(_, _, _, _) => todo!(),
    rustc_hir::ExprKind::Match(_, _, _) => todo!(),
    rustc_hir::ExprKind::Closure(_, _, _, _, _) => todo!(),
    rustc_hir::ExprKind::Block(Block {stmts, expr, targeted_by_break,..}, None) => {
      assert_eq!(targeted_by_break, &false, "Don't know how to handle breaks");

      stmts.iter().for_each(|stmt| {
        match stmt.kind {
            rustc_hir::StmtKind::Local(_) => todo!(),
            rustc_hir::StmtKind::Item(_) => todo!(),
            rustc_hir::StmtKind::Expr(expr) => {
              worklist.push_front(expr.hir_id)
            },
            rustc_hir::StmtKind::Semi(_) => todo!(),
        }
        
      });

      todo!()
    },
    rustc_hir::ExprKind::Block(_, _) => todo!(),
    rustc_hir::ExprKind::Assign(_, _, _) => todo!(),
    rustc_hir::ExprKind::AssignOp(_, _, _) => todo!(),
    rustc_hir::ExprKind::Field(_, _) => todo!(),
    rustc_hir::ExprKind::Index(_, _) => todo!(),
    rustc_hir::ExprKind::Path(_) => todo!(),
    rustc_hir::ExprKind::AddrOf(_, _, _) => todo!(),
    rustc_hir::ExprKind::Break(_, _) => todo!(),
    rustc_hir::ExprKind::Continue(_) => todo!(),
    rustc_hir::ExprKind::Ret(_) => todo!(),
    rustc_hir::ExprKind::InlineAsm(_) => todo!(),
    rustc_hir::ExprKind::Struct(_, _, _) => todo!(),
    rustc_hir::ExprKind::Repeat(_, _) => todo!(),
    rustc_hir::ExprKind::Yield(_, _) => todo!(),
    rustc_hir::ExprKind::Err => todo!(),
}
}

#[cfg(test)]
mod test {
    use std::collections::HashMap;

    use crate::test_with_rustc::with_expr;

    use super::calculate_reachable_definitions;
    use pretty_assertions as pretty;
    use quote::quote;

    #[test]
    fn test_single() {
        with_expr(
            &quote! {
              fn test() {
                let mut a = 1;
                a = 3;
              }
            }
            .to_string(),
            |expr, tcx, local_ctx| {
                let res = calculate_reachable_definitions(&tcx, expr);
                pretty::assert_eq!(res, HashMap::new());
            },
        )
        .unwrap();
    }
}
