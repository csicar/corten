namespace Corten

/- Variables and Values -/

/- names for variables -/
abbrev PVar := String

inductive Val where
  | bool (b : Bool)
  | int  (i : Int)
  | ref  (x : PVar)
  deriving DecidableEq

instance : Coe Bool Val := ⟨Val.bool⟩
instance : Coe Int Val  := ⟨Val.int⟩

/- Expressions and Commands -/

/-- binary operations -/
inductive BinOp where
  | eq | and | lt | add | sub
  deriving DecidableEq

inductive Expr where
  | const (v : Val)
  | var (n : PVar)
  | binop (l : PVar) (op : BinOp) (r : PVar)
  | deref (x : PVar) -- `*x`
  deriving DecidableEq


instance : Coe Val   Expr := ⟨Expr.const⟩
instance : Coe PVar Expr := ⟨Expr.var⟩


def BinOp.eval : BinOp → Val → Val → Option Val
  | BinOp.eq,  v₁,          v₂          => some <| Val.bool <| v₁ = v₂
  | BinOp.and, Val.bool b₁, Val.bool b₂ => some <| Val.bool <| b₁ ∧ b₂
  | BinOp.lt,  Val.int i₁,  Val.int i₂  => some <| Val.bool <| i₁ < i₂
  | BinOp.add, Val.int i₁,  Val.int i₂  => some <| Val.int <| i₁ + i₂
  | BinOp.sub, Val.int i₁,  Val.int i₂  => some <| Val.int <| i₁ - i₂
  | _,         _,           _           => none


inductive Stmt where
  | skip
  -- assign `x = e`
  | ass (x : PVar) (e : Expr)
  -- assign `*x = z`
  | ass_ref (x : PVar) (z : PVar)
  | seq (c₁ c₂ : Stmt)
  | cond (x : PVar) (cₜ cₑ : Stmt)
  | while (x : PVar) (c : Stmt)
  | relax (Γ : Ctxt)

open Stmt

infix:150 " ::= " => ass
infix:150 " *:= " => ass_ref
infix:130 ";; "   => seq

