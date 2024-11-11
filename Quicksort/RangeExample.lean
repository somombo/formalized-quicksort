#check Std.Range

-- ∀ i ∈ [4:10], pred i

#check 6 ∈ [4:10]
open Std

class Membership' (α : outParam (Type u)) (γ : Type v) where
  /-- The membership relation `a ∈ s : Prop` where `a : α`, `s : γ`. -/
  mem : γ → α → Prop

instance (n : Nat) : Membership (Fin n) Range where
  mem r i := r.start ≤ i.val ∧ i.val < r.stop
