


variable {α : Type} [DecidableEq α]
variable {β : Type} [DecidableEq β]
variable {γ : Type} [DecidableEq γ]


inductive Udp α β where
  | empty : Udp α β
  | update : α → β → Udp α β → Udp α β

notation:max f:60  "[" a:min " ≫ " b:min "]" => Udp.update f a b

variable {m : Udp α β}
variable {a : α}
variable {b : β}

def Udp.forwardInternal m (needle : α) (acc : Option β) := 
  match m with
  | empty => acc
  | update i b tail => 
    if i == needle
      then tail.forwardInternal needle (some b)
      else tail.forwardInternal needle acc

def Udp.forward : Udp α β → α → Option β
  := (Udp.forwardInternal · · none)