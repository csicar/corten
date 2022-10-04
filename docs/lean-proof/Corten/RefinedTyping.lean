import Corten.Language
import Corten.Util

namespace Corten
abbrev LVar := String


inductive BaseTy where
  | Bool
  | Int
  | Ref (target: BaseTy) 
  deriving DecidableEq


inductive Pred where
  | const (v: Val) : Pred
  | var (lvar: LVar) : Pred
  | binop (left: Pred) (op: BinOp) (right: Pred) : Pred
  | not (inner: Pred) : Pred

notation:40 l " ≐  " r => Pred.binop l BinOp.eq r

def Pred.eval (pred: Pred) (assignment : Map LVar Val) (free_vars : LVar → Val): Option Val :=
    match pred with
    | Pred.const v => v
    | Pred.var x => (assignment.forward x).getD (free_vars x) |> some
    | Pred.not p => 
        match p.eval assignment free_vars with
          | some (Val.bool v) => some <| Val.bool v
          | _ => none
    | Pred.binop l op r => 
          match l.eval assignment free_vars, r.eval assignment free_vars with
            | some lv, some rv => op.eval lv rv
            | _, _ => none

structure Ctxt where
  μ : Map PVar LVar
  φ : Pred
  b : Map PVar BaseTy


variable (Γ : Ctxt) in
def Val.ty : Val → Option BaseTy
  | Val.bool _ => BaseTy.Bool
  | Val.int _  => BaseTy.Int
  | Val.ref x => BaseTy.Ref ((Γ.b.forward x).getD BaseTy.Bool)

def Ctxt.updateCtxt (Γ : Ctxt) (pvar : PVar) (lvar: LVar) : Ctxt :=
    Ctxt.mk (Map.update Γ.μ pvar lvar) Γ.φ Γ.b

notation:max Γ:60 "[" a " ↦ " α "]" => Ctxt.updateCtxt Γ a α

def appendFormula (Γ : Ctxt) (φ : Pred) : Ctxt :=
  Ctxt.mk Γ.μ (Pred.binop φ BinOp.and Γ.φ) Γ.b

def emptyCtx := Ctxt.mk (Map.empty) (Pred.const true) ∅

instance : EmptyCollection Ctxt := ⟨emptyCtx⟩

notation:50 Γ " ,, " φ => appendFormula Γ φ 

inductive fresh (Γ : Ctxt) : (α: LVar) → Prop where
  | not_in_dom : (Map.inDom α Γ.μ = false) → fresh Γ α

structure Ty where
  baseTy: BaseTy
  lvar: LVar
  predicate: Pred

notation:max "{ " v " : " b " | " φ "}" => Ty.mk b v φ

example := { "a" : BaseTy.Int | Pred.const true }

def BinOp.basety (op: BinOp) :=
  match op with
  | BinOp.eq  => BaseTy.Bool
  | BinOp.and => BaseTy.Bool
  | BinOp.lt => BaseTy.Bool
  | BinOp.add => BaseTy.Int
  | BinOp.sub => BaseTy.Int

def BinOp.type (τ : BaseTy) (op : BinOp) : Option BaseTy :=
  match op, τ with
  | BinOp.eq, τ => BaseTy.Bool
  | BinOp.and, BaseTy.Bool => BaseTy.Bool
  | BinOp.lt, BaseTy.Int => BaseTy.Bool
  | BinOp.add, BaseTy.Int => BaseTy.Int
  | BinOp.sub, BaseTy.Int => BaseTy.Int
  | _, _ => none


def symbolic_execute (Γ : Ctxt) (e : Expr) : Option Pred :=
  match e with
  | Expr.const v => Pred.const v
  | Expr.var x => Γ.μ.forward x |> .map Pred.var
  | Expr.deref x => none
  | Expr.binop x₁ op x₂=> 
    let l := Γ.μ.forward x₁
    let r := Γ.μ.forward x₂
    match l, r with
     | some lx, some rx => Pred.binop (Pred.var lx) op (Pred.var rx)
     | _, _ => none

notation:max "⟦" e "⟧{" Γ "}" => symbolic_execute Γ e

def form_pred (Γ: Ctxt) (e: Expr) (α : LVar) : Pred :=
  match ⟦e⟧{Γ} with
  | some sym => Pred.var α ≐ sym
  | none => Pred.const <| Val.bool true

example : ⟦ Expr.const (Val.int 2) ⟧{Γ} = Pred.const (Val.int 2) := by simp [symbolic_execute]

example {x : PVar } : ⟦ Expr.var x ⟧{Γ[x ↦ α]} = Pred.var α := by 
  simp [symbolic_execute, Ctxt.updateCtxt]
  simp [update_on_forward, Option.map]

set_option hygiene false  -- HACK: allow forward reference
local notation:60 Γ " ⊢ " e " : " τ:61 => Typing Γ e τ

inductive Expr.Typing (Γ : Ctxt) : Expr → Ty → Prop where
  | sym_exec :
      fresh Γ α →
      Γ ⊢ e : { α : b | form_pred Γ e α }
  | deref :
      Γ ⊢ Expr.var x : { β : BaseTy.Ref b | Pred.var β ≐ Pred.const (Val.ref y) } →
      Γ ⊢ Expr.var y : τ →
      Γ ⊢ Expr.deref x : τ
  -- | const : fresh Γ α →
  --    Γ ⊢ (v : Val) : { α : v.ty | (Pred.var α) ≐ (Pred.const v)  }
  -- | var  :
  --   fresh Γ α →
  --   Γ.μ.forward x = some β →
  --   Γ.b.forward x = some b →
  --   Γ ⊢ var x : { β : b | Pred.var β ≐ Pred.var α}
  -- | binop :
  --   Γ.μ.forward x1 = some α →
  --   Γ.b.forward x1 = some b →
  --   Γ.μ.forward x2 = some β →
  --   Γ.b.forward x2 = some b →
  --   op.type b = some bᵣ →
  --   fresh Γ γ →
  --   Γ ⊢ binop x1 op x2 : { γ : bᵣ | Pred.var γ ≐ (Pred.binop (Pred.var α) op (Pred.var β))}

notation:10 Γ " ⊢ " e " : " τ => Expr.Typing Γ e τ



inductive SubCtx : Ctxt → Ctxt → Prop where
  | refl : SubCtx Γ Γ
  -- | sub 
  --   (sub : ∀ x, (Γ.μ.forward x).isSome → (Γ'.μ.forward x).isSome)
  --   (hvalid : ∀ m : LVar → Val, Γ.φ.eval (fun α => 
  --               let x := Γ.μ.inverse.forward α;
  --               let β := Γ'.μ.forward x.get!;
  --               m β.get!
  --     )): SubCtx Γ Γ'

notation:50 Γ " ≼ " Γ' => SubCtx Γ Γ'

local notation:60 Γ " ⊢ " c " ⇒ " Γ' => WF Γ c Γ'

inductive Stmt.WF : Ctxt -> Stmt → Ctxt → Prop where
  | skip : Γ ⊢ skip ⇒ Γ
  | ass  :
    Expr.Typing Γ e ({ α : b | φ1 }) →
    Γ ⊢ x ::= e ⇒ Γ[x ↦ α],, φ1
  | assStrong  :
    Γ.μ.forward z = some β →
    fresh Γ γ →
    Expr.Typing Γ (Expr.var x) ({ α : BaseTy.Ref b | Pred.var α ≐ Pred.const (Val.ref y) }) →
    Γ ⊢ x *:= z ⇒ Γ[x ↦ α],, Pred.var α ≐ Pred.const (Val.ref y) 
  | seq
      (hl: Γ ⊢ c1 ⇒ Γ1)
      (hr: Γ1 ⊢ c2 ⇒ Γ2) :
      Γ ⊢ (c1 ;; c2) ⇒ Γ2
  | condwf :
    (Γ ⊢ cₜ ⇒ Γ') →
    (Γ ⊢ cₑ ⇒ Γ') →
    Γ.μ.forward x = α →
    Γ ⊢ Stmt.cond x cₜ cₑ ⇒ Γ'
  | whilewf :
    Γ.μ.forward x = α →
    (Γ ⊢ c ⇒ Γ') →
    SubCtx Γ Γ' →
    Γ ⊢ Stmt.while x c ⇒ Γ
  | subctx :
    (SubCtx Γ' Γ) →
    Γ ⊢ Stmt.relax Γ ⇒ Γ'

notation:60 Γ " ⊢ " c " ⇒ " Γ' => Stmt.WF Γ c Γ'