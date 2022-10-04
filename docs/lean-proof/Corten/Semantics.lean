import Corten.Language
import Corten.Util

namespace Semantics
open Corten

abbrev State := Map PVar Val
namespace Corten

variable (σ : State) in
def Expr.eval : Expr → Option Val
  | Expr.const v => some v
  | Expr.var x   => σ.forward x
  | Expr.deref x   => match σ.forward x with
    | some (Val.ref y) => σ.forward y
    | _ => none
  | Expr.binop x₁ op x₂ => match σ.forward x₁, σ.forward x₂ with
    | some v₁, some v₂ => op.eval v₁ v₂
    | _,       _       => none

notation:max "⟦" e "⟧(" σ ")" => Expr.eval σ e


example : ∃ v, ⟦Expr.deref "x"⟧(∅["x" ≫ Val.ref "y"]["y" ≫ Val.int 234]) = v := 
  by
    simp [List.filterMap, Expr.eval, update_on_forward]
    rw [update_comm]
    simp [update_on_forward]
    rw [<-update_comm _]
    simp [update_on_forward]
    apply Exists.intro (some (Val.int 234))
    rfl
    have asd : "x" ≠ "y" := by simp_all
    exact asd
    have asd : "x" ≠ "y" := by simp_all
    exact asd

set_option hygiene false  -- HACK: allow forward reference
local notation:60 "⟨" c ", " σ "⟩"  " ⇒ ⟨" c'  " , " σ' " ⟩" => Smallstep c σ c' σ'

inductive Smallstep : Stmt → State → Stmt → State → Prop where
  | ass :
    ⟨ x ::= e, σ⟩ ⇒ ⟨ Stmt.skip, (σ.update x (⟦e⟧(σ))) ⟩
  | assRef (h_ref : σ.forward x = some (Val.ref y)):
    ⟨ x *:= y, σ⟩ ⇒ ⟨Stmt.skip, σ.update y (⟦y⟧(σ))⟩
  | seqInner (h₁ : ⟨ c₁ , σ⟩ ⇒ ⟨ c₁', σ' ⟩ ) :
    ⟨ c₁ ;; c₂ , σ ⟩ ⇒ ⟨ c₁' ;; c₂ , σ' ⟩ 
  | seqElim :
    ⟨ Stmt.skip ;; c, σ ⟩ ⇒ ⟨ c, σ ⟩ 
  | ifTrue (hb : σ.forward x = some (Val.bool true)) :
    ⟨ Stmt.cond x cₜ cₑ, σ⟩ ⇒ ⟨ cₜ, σ ⟩
  | ifFalse (hb : σ.forward x = some (Val.bool false)) :
    ⟨ Stmt.cond x cₜ cₑ, σ⟩ ⇒ ⟨ cₜ, σ ⟩
  | whileSS :
    ⟨ Stmt.while x c, σ⟩ ⇒ ⟨ Stmt.cond x (Stmt.while x c) Stmt.skip, σ⟩
  | relaxSS : (Γ' : Ctxt) → ⟨ Stmt.relax Γ', σ⟩ ⇒ ⟨ Stmt.skip, σ⟩ 

notation:60 "⟨" c ", " σ "⟩"  " ⇒ ⟨" c'  " , " σ' " ⟩" => Smallstep c σ c' σ'