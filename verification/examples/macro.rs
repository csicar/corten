#![feature(adt_const_params)]
extern crate runtime_library;
use runtime_library::ty;

fn main() {
    // let message = "Test";
    // println!("{}", message)
    ()
}



fn t(a: ty! {ra: i32 | ra < 10}) -> ty! {v: i32 | v > 0} {
    2 as ty!{v : i32 | v > 0}
}

// #[refined]
// fn max(a: ty!{ra : i32 | true}, b: ty!{rb :i32 | true}) -> ty!(v: i32 | v >= ra && v >= rb) {
//     if a > b {
//         a
//     } else {
//         b
//     }
// }
