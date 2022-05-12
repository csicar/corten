
Typing Rules as Implemented
===========================

## VAR

```math
\text{VAR}
\frac
  {
    \begin{aligned}
      x: \{ v : b \mid p\} \in \Gamma \qquad 
     
    \end{aligned}
  }
  {\Gamma \vdash x : \{v':b \mid p \wedge v = v'\} \Rightarrow \Gamma}
```

## IF

```math
\text{IF-Then}
\frac
  {
    \begin{aligned}
      \Gamma_c, \neg c \vdash c_e : \tau_e \Rightarrow \Gamma_e \\
      \Gamma_c, c \vdash c_t :\tau_t \Rightarrow \Gamma_t  
        & \qquad \Gamma_e \preceq \Gamma_t\\
      \Gamma \vdash c : \text{bool} \Rightarrow \Gamma_c 
        & \qquad \Gamma_c,\neg c \vdash \tau_e \preceq \tau_t  \\
     
    \end{aligned}
  }
  {\Gamma \vdash \text{if } c \text{ then }c_t\text{ else } c_e : \tau \Rightarrow \Gamma_t}
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

## SEQ


```math
\text{SEQ}
\frac
  {
    \begin{aligned}
      \Gamma \vdash s_1 : \tau_{dontcare} \Rightarrow \Gamma'
      \qquad
      \Gamma' \vdash \bar s : \tau \Rightarrow \Gamma''
    \end{aligned}
  }
  {\Gamma \vdash s_1 ; \bar s : \tau \Rightarrow \Gamma''}
```
This also works with variables declarations: In that case $`\Gamma'`$ contains a new variable

## ASSIGN


```math
\text{ASSIGN}
\frac
  {
    \begin{aligned}
      \Gamma \vdash e : \tau \Rightarrow \Gamma'
    \end{aligned}
  }
  {\Gamma \vdash x = e : \tau \Rightarrow \Gamma' [x \rightarrow \tau]}
```

## WHILE

```math
\frac
{\Gamma_!, c \vdash s \Rightarrow \Gamma_! \qquad \Gamma_b \preceq \Gamma_!}
{\Gamma_b \vdash \texttt{while}(c) s \Rightarrow \Gamma_!,\neg c}
```

## BinOp

```math
\text{BinOP}
\frac
  {
    \begin{aligned}
      \Gamma \vdash e_1 : \{v:b \mid \varphi_1\} \Rightarrow \Gamma \\
      \Gamma \vdash e_2 : \{v:b \mid \varphi_2\} \Rightarrow \Gamma
    \end{aligned}
  }
  {\Gamma \vdash e_1 + e_2 : \{ v: b \mid v == [e_1] + [e_2]\} \Rightarrow \Gamma'}
```

Subtyping Rules as Implemented
==============================

```math
\text{$\preceq$-BASE}
\frac
  {\neg\text{SMT-SAT}([\Gamma] \wedge v_1 = v_2 \wedge [e_1]\wedge \neg[e_2] )}
  {\Gamma \vdash \{ v_1: b \mid e_1\} \preceq \{ v_2: b \mid e_2\}}
```


Refinement Context Subtyping as Implemented
===========================================


```math
\text{$\preceq$-BASE}
\frac
  {\neg\text{SMT-SAT}([\Gamma] \wedge \neg [\Gamma'] )}
  {\Gamma  \preceq \Gamma'}
```
