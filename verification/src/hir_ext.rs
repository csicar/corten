use rustc_hir as hir;
use rustc_middle::ty::TyCtxt;
use rustc_span as span;
use rustc_span::source_map;
use tracing::info;

//////////////////// Ty

pub trait TyExt<'a> {
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
                    let binder = binder_const_arg.try_into_const_string(&tcx).unwrap();
                    let predicate = body_const_arg.try_into_const_string(&tcx).unwrap();
                    info!(?base_type, ?binder, ?predicate, "found refinement");
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
    fn try_into_symbol(&'a self) -> Option<span::Symbol>;
}

impl<'a> ExprExt<'a> for hir::Expr<'a> {
    fn try_into_symbol(&'a self) -> Option<span::Symbol> {
        if let hir::Expr {
            kind:
                hir::ExprKind::Lit(source_map::Spanned {
                    node: rustc_ast::LitKind::Str(symbol, _),
                    ..
                }),
            ..
        } = self
        {
            Some(*symbol)
        } else {
            None
        }
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
                hir::Node::Expr(expr) => Some(expr),
                e => None,
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
