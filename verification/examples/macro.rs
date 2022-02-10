extern crate runtime_library;
use runtime_library::ty;


fn main() {
  let message = "Test";
  println!("{}", message)
}

struct Point {
  x: i32,
  y: i32
}

fn  abs(i: i32) -> ty!(r: i32 | r >= 0) {

}

fn update_x(a: &mut Point, x: i32) -> ty!(Unit<a.x == x>) {
  a.x = x;
}