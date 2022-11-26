
use runtime_library::*;

fn increment(
    a : ty!{ v : i32 | v > 0 }
) -> ty!{ r : i32 | r > v } {
    a + 1 // try replace this with `a-1`
}

fn max(
    a : ty!{ av: i32 | true },
    b: ty!{ bv: i32 | true }
) -> ty!{ v: i32 | v >= av && v >= bv } {
    if a > b { 
        a as ty!{ x : i32 | x >= av && x >= bv }
    } else { 
        b
    }
}

fn inc(
p : &mut ty!{ a : i32 | true => b | b == a + 1 }
) -> ty!{ v : () } {
    *p = *p + 1; ()
}