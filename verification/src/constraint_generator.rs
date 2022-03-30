use anyhow::anyhow;
use rsmt2::SmtConf;
use rustc_ast as ast;
use rustc_hir as hir;
use rustc_hir::Ty;
use rustc_hir::{Expr, ExprKind};
use rustc_middle::ty::{query::TyCtxtAt, TyCtxt};
use rustc_span::source_map::Spanned;
use syn::__private::ToTokens;

use crate::refinements::{extract_refinement_type_from_type_alias, RefinementType};

macro_rules! sexp {
    ($assert:tt) => {{
        stringify! {$assert}.to_string()
    }};
}

pub fn encode_smt(expr: &syn::Expr) -> String {
    match expr {
        syn::Expr::Binary(syn::ExprBinary {left, right, op, ..}) => {
            let smt_op = match op {
                syn::BinOp::Add(_) => "+",
                syn::BinOp::Sub(_) => "-",
                syn::BinOp::Mul(_) => "*",
                syn::BinOp::Div(_) => "/",
                syn::BinOp::And(_) => "&&",
                syn::BinOp::Or(_) => "||",
                syn::BinOp::Eq(_) => "=",
                syn::BinOp::Lt(_) => "<",
                syn::BinOp::Le(_) => "<=",
                syn::BinOp::Ge(_) => ">=",
                syn::BinOp::Gt(_) => ">",
                _ => todo!()
            };
            format!("({} {} {})", smt_op, encode_smt(left), encode_smt(right))
        },
        syn::Expr::Lit(syn::ExprLit {lit, ..}) => match lit {
            syn::Lit::Str(_) => todo!(),
            syn::Lit::ByteStr(_) => todo!(),
            syn::Lit::Byte(_) => todo!(),
            syn::Lit::Char(_) => todo!(),
            syn::Lit::Int(lit) => lit.to_token_stream().to_string(),
            syn::Lit::Float(_) => todo!(),
            syn::Lit::Bool(_) => todo!(),
            syn::Lit::Verbatim(_) => todo!(),
        },
        syn::Expr::Path(syn::ExprPath {path: syn::Path {segments, ..}, ..}) => 
            match segments.first() {
                Some(syn::PathSegment {ident, ..})  => format!("{}", ident),
                _ => todo!()
            },
        other => todo!("expr: {:?}", expr),
    }
}

pub fn type_check_node<'a, 'tcx>(
    node: &'a hir::Node<'tcx>,
    tcx: &'a TyCtxt<'tcx>,
    expected_type: &'a RefinementType,
) -> anyhow::Result<Vec<String>>
where
    'tcx : 'a,
{
    match node {
        hir::Node::Expr(expr) => type_check(expr, tcx, expected_type),
        hir::Node::Param(_) => todo!(),
        hir::Node::Item(_) => todo!(),
        hir::Node::ForeignItem(_) => todo!(),
        hir::Node::TraitItem(_) => todo!(),
        hir::Node::ImplItem(_) => todo!(),
        hir::Node::Variant(_) => todo!(),
        hir::Node::Field(_) => todo!(),
        hir::Node::AnonConst(_) => todo!(),
        hir::Node::Stmt(_) => todo!(),
        hir::Node::PathSegment(_) => todo!(),
        hir::Node::Ty(_) => todo!(),
        hir::Node::TraitRef(_) => todo!(),
        hir::Node::Binding(_) => todo!(),
        hir::Node::Pat(_) => todo!(),
        hir::Node::Arm(_) => todo!(),
        hir::Node::Block(_) => todo!(),
        hir::Node::Local(_) => todo!(),
        hir::Node::Ctor(_) => todo!(),
        hir::Node::Lifetime(_) => todo!(),
        hir::Node::GenericParam(_) => todo!(),
        hir::Node::Visibility(_) => todo!(),
        hir::Node::Crate(_) => todo!(),
        hir::Node::Infer(_) => todo!(),
    }
}

fn type_check<'a, 'tcx>(
    expr: &'a Expr<'tcx>,
    tcx: &'a TyCtxt<'tcx>,
    expected_type: &'a RefinementType,
) -> anyhow::Result<Vec<String>>
where
    // 'tcx at least as long as 'a
    'tcx: 'a,
{
    match &expr.kind {
        ExprKind::Let(hir::Let {
            pat,
            ty,
            init,
            span,
            ..
        }) => {
            let refinement_type = ty
                .map(|t| extract_refinement_type_from_type_alias(t, &tcx))
                .ok_or(anyhow!(
                    "LiquidRust requires fully specified types. Missing on {:?}",
                    span
                ))??;
            type_check(init, tcx, &refinement_type)
        }
        ExprKind::Block(hir::Block { stmts, expr, .. }, _) => match (stmts, expr) {
            ([], Some(result_expression)) => type_check(result_expression, tcx, expected_type),
            other => todo!(),
        },
        ExprKind::Lit(Spanned { node, span }) => match node {
            ast::LitKind::Int(val, _) => Ok(vec![
                "(declare-const v Int)".to_string(),
                format!("(assert (=> (= v {}) ({})))", val, encode_smt(&expected_type.predicate))]),
            ast::LitKind::Str(_, _) => todo!(),
            ast::LitKind::ByteStr(_) => todo!(),
            ast::LitKind::Byte(_) => todo!(),
            ast::LitKind::Char(_) => todo!(),
            ast::LitKind::Float(_, _) => todo!(),
            ast::LitKind::Bool(_) => todo!(),
            ast::LitKind::Err(_) => todo!(),
        },
        ExprKind::Path(_) => todo!(),
        ExprKind::Box(_) => todo!(),
        ExprKind::ConstBlock(_) => todo!(),
        ExprKind::Array(_) => todo!(),
        ExprKind::Call(_, _) => todo!(),
        ExprKind::MethodCall(_, _, _) => todo!(),
        ExprKind::Tup(_) => todo!(),
        ExprKind::Binary(_, _, _) => todo!(),
        ExprKind::Unary(_, _) => todo!(),
        ExprKind::Cast(_, _) => todo!(),
        ExprKind::Type(_, _) => todo!(),
        ExprKind::DropTemps(_) => todo!(),
        ExprKind::If(_, _, _) => todo!(),
        ExprKind::Loop(_, _, _, _) => todo!(),
        ExprKind::Match(_, _, _) => todo!(),
        ExprKind::Closure(_, _, _, _, _) => todo!(),
        ExprKind::Assign(_, _, _) => todo!(),
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
    }
}

#[test]
fn test() {
    let parser = ();

    let conf = SmtConf::default_z3();
    let mut solver = conf.spawn(parser).unwrap();
    solver.declare_const("a", "Int").unwrap();

    let ass = sexp! {
      (> a 2)
    };
    dbg!(ass.clone());
    solver.assert(ass);

    let is_sat = solver.check_sat().unwrap();
    println!("{}", is_sat);
    let model = solver.get_model().unwrap();
    println!("{:?}", model);
}
