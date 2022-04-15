#![feature(adt_const_params)]

pub type Refinement<T, const BINDER: &'static str, const REFINEMENT: &'static str> = T;

pub type MutRefinement<
    T,
    const BINDER_BEFORE: &'static str,
    const REFINEMENT_BEFORE: &'static str,
    const BINDER_AFTER: &'static str,
    const REFINEMENT_AFTER: &'static str,
> = T;

#[macro_export]
macro_rules! ty {
  ($i:ident : $base_ty:ty | $pred:expr) => {
      $crate::Refinement< $base_ty, {stringify! { $i }}, {stringify! { $pred }}>
  };
  ($i:ident : $base_ty:ty | $pred:expr => $i2: ident  | $pred2:expr) => {
      $crate::MutRefinement< $base_ty, {stringify! { $i }}, {stringify! { $pred }}, {stringify! { $i2 }}, {stringify! {$pred2}}>
  };
  ($base_ty:ty) => {
      $crate::Refinement<$base_ty, "_", "true">
  };
  ($base_ty:ty [ $inner:tt ]) => {
      $crate::Refinement<$base_ty, "_", {stringify!{ $inner}}>
  }
}

mod test {

    fn test_mut(a: &mut ty! {av : i32 | av > 0 => af | af > av }) {

    }
}
