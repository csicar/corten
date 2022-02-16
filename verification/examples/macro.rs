extern crate runtime_library;
use runtime_library::{refined, refined2};

fn main() {
    let message = "Test";
    println!("{}", message)
}

struct Point {
    x: i32,
    y: i32,
}

#[refined]
fn t(a: ty!(i32 | a > 2)) -> i32 {
 2
}
