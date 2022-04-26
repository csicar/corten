
Typing Rules as Implemented
===========================

## IF

```math
\text{IF-Then}
\frac
  {
    \begin{aligned}
      \Gamma_c, \neg c \vdash c_e : \tau_e \Rightarrow \Gamma_e \\
      \Gamma_c, c \vdash c_t :\tau_t \Rightarrow \Gamma_t  
        & \qquad \Gamma_e \preceq \Gamma'\\
      \Gamma \vdash c : \text{bool} 
        & \qquad \Gamma_c,\neg c \vdash \tau_e \preceq \tau_t  \\
     
    \end{aligned}
  }
  {\Gamma \vdash \text{if } c \text{ then }c_t\text{ else } c_e : \tau \Rightarrow \Gamma'}
```

Analogous for $`\text{IF-Else}`$

We try to be a little clever here:
instead of requiring the user to specify the type of the if-then-else expression all the time
we make sure that it is sufficient, that either one of the branches has a general enough type to
cover both.
This means, that either else_ty ≼ then_ty OR then_ty ≼ else_ty. The complete expression
then has the lesser of both types.
subtype checking is done in the refinement type context of the subtype, because
it needs to show, that it is a sub type of the postulated complete type *in its context*

Subtyping Rules as Implemented
==============================

```math
\text{$\preceq$-BASE}
\frac
  {\text{SMT-SAT}([\Gamma] \wedge v_1 = v_2 \wedge [e_1]\wedge \neg[e_2] )}
  {\Gamma \vdash \{ v_1: b \mid e_1\} \preceq \{ v_2: b \mid e_2\}}
```

```math
