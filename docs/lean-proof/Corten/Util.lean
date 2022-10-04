-- maybe use?
-- import Lean.Data.AssocList

namespace Function
  
  def update [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
    fun a' => if a' = a then b else f a'

  -- notation:max f:60 "[" a " ▸ " b "]" => update f a b
end Function

structure Map (α β : Type u) [DecidableEq α] [DecidableEq β]  where
  rel : List (α × β)

def Map.hasDecEq {α : Type u} [DecidableEq α] [DecidableEq β]  : (a b : Map α β) → Decidable (Eq a b)
  | ⟨a⟩  , ⟨b⟩ => by
      simp
      exact List.hasDecEq a b

instance [DecidableEq α] [DecidableEq β] : DecidableEq (Map α β)
  := fun a b => Map.hasDecEq a b

def Map.forward [DecidableEq α] [DecidableEq β] (m : Map α β) : (α → Option β)
  := fun a => List.findSome? (fun x => if x.1 == a then x.2 else none) m.rel

instance (α β: Type u) [DecidableEq α] [DecidableEq β] : Coe (Map α β) (α → Option β) where
  coe := Map.forward

def Map.backward [DecidableEq α] [DecidableEq β] (m : Map α β) : (β → Option α)
  := fun b => List.findSome? (fun x => if x.2 == b then x.1 else none) m.rel

open Option

def Map.update [DecidableEq α] [DecidableEq β] (m: Map α β) (a: α) (b : Option β) : Map α β :=
  Map.mk <| List.filterMap (fun el => if el.1 == a then b.map (a, ·) else some el) m.rel
  
notation:max f:60  "[" a:min " ≫ " b:min "]" => Map.update f a b

def Map.dom [DecidableEq α] [DecidableEq β] (m : Map α β) := List.map (fun el => el.1) m.rel

def Map.img [DecidableEq α] [DecidableEq β] (m : Map α β) := List.map (fun el => el.2) m.rel


def Map.empty [DecidableEq α] [DecidableEq β] := @Map.mk α β _ _ List.nil 

instance [DecidableEq α] [DecidableEq β] : EmptyCollection (Map α β) := ⟨Map.empty⟩


def Map.inDom [DecidableEq α] [DecidableEq β] (a : α) (m : Map α β) := Map.dom m |> List.elem a
def Map.inImg [DecidableEq α] [DecidableEq β] (b : β) (m : Map α β) := Map.img m |> List.elem b

def Map.compose [DecidableEq α] [DecidableEq β] [DecidableEq γ] (m1 : Map α β) (m2 : Map β γ) : Map α γ :=
  List.filterMap (fun (a, b) => let c := m2.forward b; c.map (a, ·)) m1.rel |> Map.mk


def Map.map [DecidableEq α] [DecidableEq β] [DecidableEq γ]  [DecidableEq δ] (m: Map α β) (f : (α × β) → (γ × δ)) : Map γ δ :=
  List.map f m.rel |> Map.mk

def Map.extend [DecidableEq α] [DecidableEq β] (m: Map α β) (u : Map α β) : Map α β :=
  let asd := m.dom.append u.dom |> .filterMap (fun a => 
    let b := (m.forward a).bind (fun _ => u.forward a)
    b.map (a, ·))
  asd |> Map.mk
    -- .map (fun (a, b) => m.forward a |> fun x => x.getD b |> (a, ·)  )


theorem extend_characteristic (α β : Type u) [DecidableEq α] [DecidableEq β] (m : Map α β) (u : Map α β)
  : ∀(a: α) (b : β), 
      (m.extend u).forward a = some b → 
      (
        m.forward a = some b ∨ 
        (m.forward a= none ∧ u.forward a = some b)
      )
  := sorry

theorem extend_empty_r (α β : Type u) [DecidableEq α] [DecidableEq β] (m : Map α β)
   :    Map.extend m {} = m
  := sorry

theorem extend_empty_l (α β : Type u) [DecidableEq α] [DecidableEq β] (m : Map α β)
   :   Map.extend {} m = m
  := sorry

def Map.inverse {α β} [DecidableEq α] [DecidableEq β] (m: Map α β) : Map β α := m.map (fun (a, b) => (b, a))
  -- List.map (fun (a, b) => (b, a)) m.rel |> Map.mk

theorem bij_inverse (α β: Type u) [DecidableEq α] [DecidableEq β] (a : α) (b : β) (m : Map α β)
  : (Map.forward m a = some b) -> m.inverse.forward b = some a :=
  sorry

theorem update_inverse (α β : Type u) [DecidableEq α] [DecidableEq β] (a : α) (b : β) (m : Map α β)
  : m[a ≫ some b].inverse = m.inverse[b ≫ some a]
  := sorry

theorem inverse_emp  {α β : Type u} [DecidableEq α] [DecidableEq β] : @Map.inverse α β _ _ ∅ = ∅ := 
  by 
    simp [Map.inverse, Map.map, List.map, Map.empty, EmptyCollection.emptyCollection]


variable {α : Type} [DecidableEq α]
variable {β : Type} [DecidableEq β]
variable {γ : Type} [DecidableEq γ]




theorem compose_empty_l (m: Map β γ): Map.compose (∅ : Map α β) m = ∅ := by
  simp [Map.compose, EmptyCollection.emptyCollection, Map.empty, List.filterMap]

theorem filterMap_none_empty (l : List α) (f : α -> Option β) : (∀a, f a = none) → l.filterMap f = ∅ 
  := by
  induction l with
  | @nil => 
    simp [List.filterMap, EmptyCollection.emptyCollection]
  | @cons h t ih => 
    simp [List.filterMap]
    intro a
    simp_all [ih a]

theorem forward_empty_is_none (a : α) : (∅ : Map α β).forward a = none := by 
  simp [Map.forward, List.findSome?]

theorem compose_empty_r (m: Map α β): Map.compose m (∅ : Map β γ) = ∅ := by
  simp [Map.compose, Map.empty]
  simp [forward_empty_is_none]
  simp_all [Option.map, filterMap_none_empty, EmptyCollection.emptyCollection, Map.empty]

theorem update_on_forward (m : Map α β): m[a ≫ some v].forward a = some v := sorry

theorem update_comm (m : Map α β) {h_diff : a ≠ b }: m[a ≫ va][b ≫ vb] = m[b ≫ vb][a ≫ va] := sorry

theorem update_in_inverse (m : Map α β): 
  Map.inImg b m = false ->
  m[a ≫ some b].inverse = m.inverse[b ≫ some a] := sorry

-- Map.compose m1[α ≫ some x] m2[x ≫ ⟦e⟧(σ)]

theorem update_in_compose
  (m1 : Map α β) (m2 : Map β γ) (a : α) (b : β) (g : γ) 
  : m1[a ≫ some b].compose (m2[b ≫ some c]) = (m1.compose m2)[a ≫ c]
  := sorry