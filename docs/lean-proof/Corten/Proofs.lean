import Corten.Util
import Corten.RefinedTyping
import Corten.Semantics

open Semantics
open Corten

variable {Γ : Ctxt} {σ : State} {e: Expr} {τ : Ty} {s: Stmt} {φ : Pred}

namespace Corten


end Corten


-- σ ∷ Γ   iff   φ[μ(x) ▸ σ(x)] is satistiable
def conformance (Γ : Ctxt) (σ : State) :=
  ∃(free_vars : LVar → Val), 
    -- φ[μ(x) ▸ σ(x)] (w/ free_vars)
    (Γ.φ.eval (Γ.μ.inverse.compose σ) free_vars) = (Val.bool true)

notation:70 σ " ∷ " Γ => conformance  Γ σ

example : Map.empty ∷ emptyCtx := by 
  simp [conformance]
  apply Exists.intro (fun x => Val.bool false)
  simp [Expr.eval]

example (v: Val) : {}[x ≫ some v] ∷ {}[x ↦ α],, Pred.var α ≐ Pred.const v
  := by
  simp [conformance]
  apply Exists.intro (fun x => Val.bool false)

  -- rw [h_emp]
  have asd : Map.inverse (∅[x ↦ α] ,, Pred.var α ≐ Pred.const v).μ = ∅[α ≫ x] 
    := by 
    simp [appendFormula]
    have gf: ∅[x ↦ α].μ = ∅[x ≫ some α] := by 
      simp_all [EmptyCollection.emptyCollection]
      simp [emptyCtx]
      simp [Ctxt.updateCtxt]
    simp [gf]
    simp [update_inverse _ _ _]
    rw [inverse_emp]

  simp [asd]
  simp [update_in_compose ∅ ∅ α x v]
  simp [compose_empty_l]
  simp [appendFormula]
  simp [Ctxt.updateCtxt]
  simp [EmptyCollection.emptyCollection]
  simp [emptyCtx]
  simp [Pred.eval]
  simp [update_on_forward, Option.getD]
  simp [BinOp.eval]

-- theorem evaluation_equivalence 
--   (h : σ  ∷ Γ) :
--   (σ[ x ≫ ⟦e⟧(σ)] ∷ Γ[x ↦ α],, Pred.var α ≐ ⟦e⟧{Γ})
--   := _

theorem simp_mu 
  : (Γ[x ↦ α] ,, Pred.var α ≐ p).μ
  = Γ.μ[x ≫ α] := by 
    simp[Ctxt.updateCtxt, appendFormula]
theorem simp_phi
  : (Γ[x ↦ α] ,, Pred.var α ≐ p).φ 
  = (Pred.binop (Pred.var α ≐ p) BinOp.and Γ.φ)
  := by 
    simp[Ctxt.updateCtxt, appendFormula]
    

-- axiom asd : {a b c : Int} -> a < b ∧b < c  -> a < c


theorem conservative_reference_tracking
  (h_conf : σ ∷ Γ)
  (h_ty : Γ ⊢ Expr.var x : {α : BaseTy.Ref b | Pred.var α ≐ Pred.const (Val.ref y)})
  (h_fresh : fresh Γ α)
  : (σ.forward x = Val.ref y)
  := by 
    simp [conformance] at h_conf 
    cases h_conf with
    | intro m h_conf =>
      by simp


-- set_option trace.Meta.Tactic.simp true
-- set_option trace.Meta.Tactic.contradiction true

theorem subctx_is_conservative 
  (h_sub : Γ' ≼ Γ) (h_conf : σ ∷ Γ ) 
  : (σ ∷ Γ') 
  := by
  simp


theorem conformance_expr
  -- (h : Γ ⊢ e : τ)
  (x : PVar)
  (h_conf: σ ∷ Γ)
  (h_fresh: fresh Γ α)
  (h_wf : ∃v, ⟦e⟧(σ) = some v)
    : σ[x ≫ ⟦e⟧(σ)] ∷ Γ[x ↦ α],, (form_pred Γ e α)
   := by 
        simp [form_pred]
        cases eq_eval : ⟦e⟧{Γ} with 
        | none => sorry
        | some p => 
          simp [conformance]
          cases h_conf with
          | intro free_vars h_eval =>
            apply Exists.intro free_vars
            rw [simp_mu, simp_phi]
            cases h_fresh with
            | not_in_dom no_dom =>
              have fresh_alpha : Map.inImg α Γ.μ = false := by sorry
              rw [update_in_inverse Γ.μ fresh_alpha]
              -- have asdasdasdl : 
              --   Map.compose (Map.inverse Γ.μ)[α ≫ some x] σ[x ≫ v]
              --   = (Map.compose (Map.inverse Γ.μ) σ)[α ≫ v]
              let ⟨v, hv⟩ := h_wf
              rw [hv, update_in_compose (Map.inverse Γ.μ) σ α x v]
              rw [Pred.eval]
              split
              case h_1 hl hr => 
                simp [Pred.eval, update_on_forward, Pred.eval, Option.getD] at hl
                split at hl
                case h_2 => contradiction
                case h_1 eq eval_rv => 
                  simp at eq
                  sorry
              case h_2 h =>
                sorry


theorem prevervation_of_conformance
  (h_ty : Γ ⊢ c ⇒ Γ2)
  (h_conf : σ ∷ Γ) 
  (h_trans : ⟨c, σ⟩ ⇒ ⟨ c1,  σ1⟩ ) : 
    ∃ Γ1, ((σ1 ∷ Γ1) ∧ (Γ1 ⊢ c1 ⇒ Γ2))
  := by
    induction h_trans generalizing Γ2 with
    | @ass x e σ =>
      apply Exists.intro Γ2
      apply And.intro
      case right => simp [Stmt.WF.skip]
      -- | left => simp
      -- | right => simp
      cases h_ty with
      | ass ht => 
        cases ht with
        | sym_exec h_fresh =>
          have is_some : ∃ v, ⟦e⟧(σ) = some v := sorry -- this assumes that the `e` uses operators correctly
          apply conformance_expr _ h_conf h_fresh is_some
        | @deref x _ β y _ h1 h2 =>
          have is_some : ∃ v, ⟦e⟧(σ) = some v := sorry -- this assumes that the `e` uses operators correctly
          cases h2 with
          | sym_exec hi =>
            have ad := conformance_expr y h_conf hi is_some
            cases ad with
            | intro => 
              simp
            -- have eq_y : ⟦Expr.deref x⟧(σ) = some (Val.ref y) := by 
            --   simp [Expr.eval]
            --   cases hrd : σ.forward x with
            --   | none => sorry -- σ must contain x
            --   | some sus_y => 
            --     cases sus_y with
            --     | bool => sorry -- σ must contain ref x
            --     | int => sorry -- σ must contain ref x
            --     | ref z => simp
            --     simp
    | assRef heval =>
      simp
      cases h_ty with
      | assStrong hevale hfresh hty =>
        simp
    | @seqInner c1 σ c1' σ' c2 h1 h_ih =>
      cases h_ty with
      | @seq _ _ Γ1 _ _ hl hr =>
        let ⟨Γ1', ⟨inner_conf, inner_trans⟩ ⟩  := @h_ih _ hl h_conf 
        apply Exists.intro Γ1'
        apply And.intro inner_conf
        apply Stmt.WF.seq inner_trans hr
    | @seqElim =>
      cases h_ty
      case seq c σ Γ1 hl hr => 
        cases hl
        case skip =>
          apply Exists.intro Γ
          apply And.intro h_conf hr
    | @ifTrue x ct ce σ ih =>
      cases h_ty with
      | condwf ht he hexec =>
        apply Exists.intro Γ
        apply And.intro h_conf
        exact ht
    | @ifFalse x ct ce σ ih =>
      cases h_ty with
      | condwf ht he hexec =>
        apply Exists.intro Γ
        apply And.intro h_conf
        exact ht
    | @whileSS x c σ =>
      cases h_ty with
      | @whilewf α _ _ Γ' _ hcond hbody hsub =>
        apply Exists.intro Γ
        apply And.intro h_conf

        have inner_ty:  Γ ⊢ Stmt.while x c ⇒ Γ := by 
          apply Stmt.WF.whilewf hcond hbody hsub
        apply @Stmt.WF.condwf _ _ _ _ _ α inner_ty Stmt.WF.skip hcond
    | relaxSS =>
      cases h_ty with
      | subctx hsub => 
        simp
        apply Exists.intro Γ2
        apply (fun x => And.intro x Stmt.WF.skip)
        apply subctx_is_conservative hsub h_conf