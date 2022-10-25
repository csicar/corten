fn clamp(
  a: &mut ty!{ a1 : i32 | true => a2 | a2 <= b1 }, 
  b: ty!{ b1: i32 }
) { 
  // $\Gamma_1 = (\{a \mapsto v_1, arg_0 \mapsto a_1, b \mapsto b_1\},$
  // $\quad \quad \quad \quad \quad \quad v_1 \doteq \&arg_0 \wedge \text{true} \wedge \text{true})$
  if *a > b { *a = b }
  // $\Gamma_2 = (\{a \mapsto v_1, arg_0 \mapsto {\red v_2}, b \mapsto b_1\},$
  // $\quad \quad \quad \quad {\red v_2 \leq b_1} \wedge v_1 \doteq \&arg_0 \wedge \text{true} \wedge \text{true})$
}