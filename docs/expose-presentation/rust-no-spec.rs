/// Add `b` to end of Vec `as`
fn push(as: &mut Vec<i32>, b: i32) {..}
/// Get highest value. Returns `None` for empty Vec
fn maximum(as: &Vec<i32>) -> Option<i32> {..}

fn update_exam_tries(tries: &mut Vec<i32>, new_try: i32) {
  push(&mut tries, new_try);

  match maximum(ties) {
    None => panic!("impossible"), // `tries` must at least contain `new_try`
    Some(max_mark) if max_mark < 4    => println!("puh"),
    _              if tries.len() > 3 => println!("Härtefallantrag?"),
    _                                 => println!("versuch's nochmal"),
  }
}