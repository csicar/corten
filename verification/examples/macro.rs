#![feature(adt_const_params)]
extern crate runtime_library;
use runtime_library::ty;

fn main() -> ty! { v: () | true } {
    // let message = "Test";
    // println!("{}", message)
    ()
}

fn test() {
    let mut a = 1;
    let mut b = 4;
    a = 3;
    while a > 3 {
      b = 3;
    }
    a = 9;
  }

// #[refined]
// fn max(a: ty!{ra : i32 | true}, b: ty!{rb :i32 | true}) -> ty!(v: i32 | v >= ra && v >= rb) {
//     if a > b {
//         a
//     } else {
//         b
//     }
// }
