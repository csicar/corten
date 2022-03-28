extern crate runtime_library;
use runtime_library::{refined};

fn main() {
    let message = "Test";
    println!("{}", message)
}

#[refined]
fn max(a: ty!{i32 | true}, b: ty!{i32 | true}) -> ty!(i32 | v >= a && v >= b) {
    if a > b {
        a
    } else {
        b
    }
}