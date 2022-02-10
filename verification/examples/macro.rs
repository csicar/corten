extern crate runtime_library;
use runtime_library::ty;


fn main() {

}

struct Point {
  x: i32,
  y: i32
}

fn update_x(a: &mut Point, x: i32) -> ty!(Unit<a.x == x>) {
  a.x = x;
}