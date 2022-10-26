fn incr() -> ty!{ w : i32 | w > 0 } {
  // $\Gamma_1 = (\set{}, \text{true})$
  let mut i = ... as ty!{ v: i32 | v >= 0};
  // $\Gamma_2 = (\set{i \mapsto v}, v > 0)$
  i = i + 1;
  // $\Gamma_3 = (\set{i \mapsto {\red{v_2}}}, v > 0 \wedge {\red{v_2 \doteq v + 1}})$
  i }