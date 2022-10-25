fn client() -> ty!{ v: i32 | v == 4 } {
  let a = 2;       // a : $\{ v_1 : i32 \mid v_1 == 2 \}$
  let b = &mut a;  // b : $\{ v_2 : &i32 \mid v_2 == &a \}$
  *b = 0; // changes a's value and type
  let c = &mut b;  // c : $\{ v_3 : &i32 \mid v_3 == &b \}$
  **c = 4; // changes a's value and type
  a
}