#![feature(adt_const_params)]

pub type Refinement<T, const B: &'static str, const R: &'static str> = T;

pub type MutRefinement<T, const B1: &'static str, const R1: &'static str, const B2: &'static str, const R2: &'static str> = T;

#[macro_export]
macro_rules! ty {
  ($i:ident : $base_ty:ty | $pred:expr) => {
      $crate::Refinement< $base_ty, {stringify! { $i }}, {stringify! { $pred }}>
  };
  ($i:ident : $base_ty:ty | $pred:expr => $i2: ident | $pred2:expr) => {
      $crate::MutRefinement< $base_ty, {stringify! { $i }}, {stringify! { $pred }}, {stringify! { $i2 }}, {stringify! { $pred2 }}>
  };
  ($base_ty:ty) => {
      $crate::Refinement<$base_ty, "_", "true">
  };
  ($base_ty:ty [ $inner:tt ]) => {
      $crate::Refinement<$base_ty, "_", {stringify!{ $inner}}>
  }
}
