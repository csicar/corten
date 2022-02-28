/// Add `b` to end of Vec `as`
fn push(as: &mut ty!(
  { before : Vec<i32> | before.len() == l} ~~> { after: Vec<i32> | after.len() == l + 1 })
  , b: i32) {..}
/// Get highest value. Returns `None` for empty Vec
fn maximum(as: &Vec<i32>) -> { r: Option<i32> | r.is_none() <=> as.len() == 0 } {..}

fn update_exam_tries(tries: &mut Vec<i32>, new_try: i32) {
  push(&mut tries, new_try);

  match maximum(ties) {
    None => proof_unrechable!(),
    Some(max_mark) if max_mark < 4    => println!("puh"),
    _              if tries.len() > 3 => println!("Härtefallantrag?"),
    _                                 => println!("versuch's nochmal"),
  }
}