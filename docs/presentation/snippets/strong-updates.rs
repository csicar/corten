fn client() -> ty!{ v: i32 | v == 4 } {
  let mut q = 3;
  let mut a = 2;       // a : $\{ v_1 : i32 \mid v_1 == 2 \}$
  let mut b = &mut a;  // b : $\{ v_2 : &i32 \mid v_2 == &a \}$
  *b = 0;              // changes a's value and type
  b = &mut q;          // b : $\{ v_2 : &i32 \mid v_2 == &q \}$
  *b = 4;              // changes q's value and type
  a
}