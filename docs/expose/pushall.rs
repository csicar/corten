fn push_all(
  a: &mut ty!({ o: Vec<i32> } ~~> { v : Vec<i32> | v.len() == o.len() + b.len()  }),
  b: &Vec<i32>) {
    ...
}
fn client() -> i32 {
    let mut a : ty!{ v: Vec<i32> | v.len() == 2 } = vec![1, 2];
    let     b : ty!{ w: Vec<i32> | w.len() == 2 } = vec![2, 3];
    push_all(a, b);
    // a : ty!{ u: Vec<i32> | u.len() == 4 }
    return a.get(5); 
    //     ^^^^^^^^  type error! 
    // Function `get` expected: `index` of type `{ v: usize | v <= 4 }`
    //                but got:   `{ v: usize | v == 5}`
}
