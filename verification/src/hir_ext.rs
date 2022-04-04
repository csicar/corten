use rustc_hir as hir;
use rustc_hir_pretty;
use rustc_middle::ty::TyCtxt;
use rustc_span as span;
use rustc_span::source_map;
use tracing::{info, instrument, trace};

//////////////////// Ty

pub trait TyExt<'a> {
    /// Try Convert a Type Alias `Refinement<i32, "b", "b > 0"> into its parts: (i32, "b", "b > 0")
    /// Return None if `self` is not an alias
    fn try_into_refinement(
        &'a self,
        tcx: &'a TyCtxt,
    ) -> Option<(&'a hir::Ty, span::Symbol, span::Symbol)>;
}

impl<'a> TyExt<'a> for hir::Ty<'a> {
    fn try_into_refinement(
        &'a self,
        tcx: &'a TyCtxt,
    ) -> Option<(&'a hir::Ty, span::Symbol, span::Symbol)> {
        if let hir::Ty {
            kind:
                hir::TyKind::Path(hir::QPath::Resolved(
                    _,
                    hir::Path {
                        res: hir::def::Res::Def(hir::def::DefKind::TyAlias, def_id),
                        segments,
                        ..
                    },
                )),
            ..
        } = self
        {
            // TODO: find Refinement alias properly
            // tcx.get_diagnostic_name
            if format!("{:?}", def_id).ends_with("]::Refinement)") {
                if let Some(hir::PathSegment {
                    args:
                        Some(hir::GenericArgs {
                            args:
                                [hir::GenericArg::Type(base_type), binder_const_arg, body_const_arg],
                            ..
                        }),
                    ..
                }) = segments.last()
                {
                    let binder = binder_const_arg
                        .try_into_const_string(&tcx)
                        .expect("could not extract binder");
                    let predicate = body_const_arg
                        .try_into_const_string(&tcx)
                        .expect("could not extract predicate");
                    Some((base_type, binder, predicate))
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            None
        }
    }
}

//////////////////// Expr

pub trait ExprExt<'a> {
    /// tries to turn Expr `"my_name"` into Symbol `my_name`
    fn try_into_symbol(&'a self) -> Option<span::Symbol>;

    /// Pretty prints the Expression
    fn pretty_print(&'a self) -> String;
}

impl<'a> ExprExt<'a> for hir::Expr<'a> {
    fn try_into_symbol(&'a self) -> Option<span::Symbol> {
        match self {
            hir::Expr {
                kind:
                    hir::ExprKind::Lit(source_map::Spanned {
                        node: rustc_ast::LitKind::Str(symbol, _),
                        ..
                    }),
                ..
            } => Some(*symbol),
            hir::Expr {
                kind:
                    hir::ExprKind::Block(
                        hir::Block {
                            stmts: [],
                            expr: Some(inner),
                            ..
                        },
                        None,
                    ),
                ..
            } => inner.try_into_symbol(),
            other => None,
        }
    }

    fn pretty_print(&'a self) -> String {
        rustc_hir_pretty::to_string(&rustc_hir_pretty::NoAnn, |state| state.print_expr(self))
    }
}

//////////////////// GenericArg

pub trait GenericArgExt<'tcx> {
    fn try_into_const_value(&'tcx self, tcx: &'tcx TyCtxt) -> Option<&'tcx hir::Expr<'tcx>>;

    // GenericType<"const str arg"> ~~> "const str arg"
    fn try_into_const_string(&'tcx self, tcx: &'tcx TyCtxt) -> Option<span::Symbol>;
}

impl<'tcx> GenericArgExt<'tcx> for hir::GenericArg<'tcx> {
    fn try_into_const_value(&'tcx self, tcx: &'tcx TyCtxt) -> Option<&'tcx hir::Expr<'tcx>> {
        if let hir::GenericArg::Const(hir::ConstArg {
            value:
                hir::AnonConst {
                    body:
                        hir::BodyId {
                            hir_id: body_hir_id,
                        },
                    ..
                },
            ..
        }) = self
        {
            match tcx.hir().get(*body_hir_id) {
                hir::Node::Expr(expr) => {
                    Some(expr)
                }
                e => {
                    None
                }
            }
        } else {
            None
        }
    }

    fn try_into_const_string(&'tcx self, tcx: &'tcx TyCtxt) -> Option<span::Symbol> {
        self.try_into_const_value(tcx)
            .and_then(|expr| expr.try_into_symbol())
    }
}
