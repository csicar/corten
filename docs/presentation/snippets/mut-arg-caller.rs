fn client(...) -> ty!{ v: () } {
  ...
  let m = 42;
  // $\Gamma_1 = (\{x \mapsto v_1, m \mapsto v_2\}, \dots \wedge v_2 \doteq 42)$
  clamp(&mut x, m);
  // $\Gamma_2 = (\{x \mapsto {\red v_3}, m \mapsto v_2\}, \dots \wedge v_2 \doteq 42 \wedge {\red v_3 \leq 5})$
  x as ty!{ v : i32 | v < 43 };
}