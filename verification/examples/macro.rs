#![feature(adt_const_params)]
extern crate runtime_library;
use runtime_library::{refined};


fn main() {
    let message = "Test";
    println!("{}", message)
}

pub type Refinement<T, const Var : &'static str, const Expr : &'static str> = T;

#[refined]
fn max(a: ty!{_1 : i32 | true}, b: ty!{_2:i32 | true}) -> ty!(v: i32 | v >= a && v >= b) {
    if a > b {
        a
    } else {
        b
    }
}