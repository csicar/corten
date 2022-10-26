#![allow(incomplete_features)]
#![feature(adt_const_params)]

use std::any::Any;

pub type Refinement<T, const B: &'static str, const R: &'static str> = T;

pub type MutRefinement<
    T,
    const B1: &'static str,
    const R1: &'static str,
    const B2: &'static str,
    const R2: &'static str,
> = T;

#[macro_export]
macro_rules! ty {
  ($i:ident : $base_ty:ty | $pred:expr) => {
      $crate::Refinement< $base_ty, {stringify! { $i }}, {stringify! { $pred }}>
  };
  ($i:ident | $pred:expr) => {
    $crate::Refinement< _, {stringify! { $i }}, {stringify! { $pred }}>
  };
  ($i:ident : $base_ty:ty | $pred:expr => $i2: ident | $pred2:expr) => {
      $crate::MutRefinement< $base_ty, {stringify! { $i }}, {stringify! { $pred }}, {stringify! { $i2 }}, {stringify! { $pred2 }}>
  };
  ($i:ident : $base_ty:ty) => {
    $crate::Refinement<$base_ty, {stringify! { $i }}, "true">
  };
  ($base_ty:ty) => {
      $crate::Refinement<$base_ty, "_", "true">
  };
  ($base_ty:ty [ $inner:tt ]) => {
      $crate::Refinement<$base_ty, "_", {stringify!{ $inner}}>
  }
}

#[macro_export]
macro_rules! ctx {
  ( $($var:ident |-> $binder:ident | $pred:expr),*) => {
      assert_ctx(&[], &[$( (&$var, {stringify!{$binder}}, {stringify!{$pred}}) ),*]);
  };
  ( $($form:expr),* ; $($var:ident |-> $binder:ident | $pred:expr),*) => {
    assert_ctx(&[$( {stringify!{$form}} ),*], &[$( (&$var, {stringify!{$binder}}, {stringify!{$pred}}) ),*]);
  };
}

#[inline(always)]
pub fn assert_ctx(_formulas: &[&'static str], _entries: &[(&dyn Any, &'static str, &'static str)]) {
}

#[allow(unused_macros)]
macro_rules! corten_assume {
    ( $pred:expr ) => {
        assume(
            $pred,
            if (!$pred) {
                unreachable!();
            } else {
                ()
            },
        );
    };
}

#[inline(always)]
pub fn assume(formula: bool, _proof: ()) {
    assert!(formula)
}

#[inline(always)]
pub fn assert(formula: bool) {
    assert!(formula)
}

#[macro_export]
macro_rules! relax_ctx {
  ( $($var:ident |-> $binder:ident | $pred:expr),*) => {
    update_ctx(&[], &[$( (&$var, {stringify!{$binder}}, {stringify!{$pred}}) ),*]);
  };
  ( $($form:expr),* ; $($var:tt |-> $binder:ident | $pred:expr),*) => {
    update_ctx(&[$( {stringify!{$form}} ),*], &[$( (&$var, {stringify!{$binder}}, {stringify!{$pred}}) ),*]);
  };
}

#[inline(always)]
pub fn update_ctx(_formulas: &[&'static str], _entries: &[(&dyn Any, &'static str, &'static str)]) {
}

#[macro_export]
macro_rules! dangling {
    ( $var:ident ) => {
        ($var,)
    };
}
