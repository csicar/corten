#![allow(dead_code)]
use runtime_library::*;

fn clamp(
  a: &mut ty!{ a1 : i32 | true => a2 | a2 <= b1 }, 
  b: ty!{ b1: i32 }
) -> ty!{ v:  () } {
  if *a > b {
      *a = b as ty!{ r | (r <= b1) }; ()
  } else {};
  ()
}

fn client() -> ty!{ v: () } {
  let mut x = 1337; let max = 32;
  clamp(&mut x, max);
  x as ty!{ v : i32 | v < 33 };
}

fn inc(
  p : &mut ty!{ a : i32 | true => b | b == a + 1 }
) -> ty!{ v : () } {
    *p = *p - 1; ()
}