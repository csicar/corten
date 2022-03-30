#![feature(adt_const_params)]
extern crate runtime_library;
use runtime_library::{refined};


fn main() {
    let message = "Test";
    println!("{}", message)
}

pub type Refinement<T, const Var : &'static str, const Expr : &'static str> = T;

#[refined]
fn max(a: ty!{ra : i32 | true}, b: ty!{rb :i32 | true}) -> ty!(v: i32 | v >= ra && v >= rb) {
    if a > b {
        a
    } else {
        b
    }
}