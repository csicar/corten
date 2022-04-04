#![feature(adt_const_params)]

pub type Refinement<T, const B: &'static str, const R: &'static str> = T;

#[macro_export]
macro_rules! ty {
  ($i:ident : $base_ty:ty | $pred:expr) => {
      $crate::Refinement< $base_ty, {stringify! { $i }}, {stringify! { $pred }}>
  };
  ($i:ident : $base_ty:ty | $pred:expr => $i2: ident : $base_ty2:ty | $pred2:expr) => {
      $crate::Refinement< $base_ty, {stringify! { $i }}, {stringify! { $pred }}>
  };
  ($base_ty:ty) => {
      $crate::Refinement<$base_ty, "v", "true">
  };
  ($base_ty:ty [ $inner:tt ]) => {
      $crate::Refinement<$base_ty, "_", {stringify!{ $inner}}>
  }
}