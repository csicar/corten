fn client(...) {
  ...
  // $\Gamma_1 = (\{x \mapsto v_1, y \mapsto v_2\}, \dots)$
  clamp(&mut x, 5);
  // $\Gamma_2 = (\{x \mapsto {\red v_3}, y \mapsto v_2\}, \dots \wedge v_3 \leq 5)$
  clamp(&mut y, 6);
  // $\Gamma_3 = (\{x \mapsto v_3, y \mapsto {\red v_4}\}, \dots \wedge v_3 \leq 5 \wedge v_4 \leq 6)$
  print!(x);
  ...
}