
-- private abbrev AllRangeHas (n a b : Nat) (pred : Fin n → Sort 0):= ∀ (i_ : Fin n), a ≤ i_ → i_ < b → pred i_
-- private abbrev ExRangeHas (n a b : Nat) (pred : Fin n → Sort 0):= ∃ (j_ : Fin n), a ≤ j_ ∧ j_ < b ∧ pred j_

abbrev RangeHas (n : Nat) (pred : Fin n → Sort 0) (a b : Nat) := ∀ (i_ : Fin n), a ≤ i_ → i_ < b → pred i_

namespace RangeHas
variable {n : Nat} {pred : Fin n → Sort 0}

protected theorem refl : ∀ a, RangeHas n pred a a := by omega

protected theorem trans : ∀ {a b c}, RangeHas n pred a b → RangeHas n pred b c → RangeHas n pred a c :=
  fun {_} {b} {_} r1 r2 i_ h1 h2 =>
    match (show b ≤ ↑i_ ∨ ↑i_ < b by omega) with
    | .inl h => r2 i_ h h2
    | .inr h => r1 i_ h1 h


@[simp] protected theorem singular {h : a < n} : RangeHas n pred a (a + 1) ↔ pred ⟨a, h⟩ := by
  constructor
  · intro r; apply r <;> simp
  · intro _ i_ _ _
    have : i_ = ⟨a, ‹_›⟩ := Fin.ext (by simp only; omega)
    simpa only [this]



protected theorem mono  (h : RangeHas n pred a b) (hi : a ≤ a') (hj : b' ≤ b) : RangeHas n pred a' b' :=
  (λ _ _ ↦ h · (by omega) (by omega))


protected theorem append (hr : pred ⟨b, hb⟩) (hrs : RangeHas n pred a b) : RangeHas n pred a (b + 1) := fun k_ h1 h2 =>
  (Nat.eq_or_lt_of_le (Nat.le_of_lt_succ h2)).elim
    ( · |> Fin.eq_of_val_eq (j := ⟨b, _⟩) |> (· ▸ hr))
    (hrs k_ h1 ·)

protected theorem unappend (hab' : a ≤ b) (h : RangeHas n pred a (b + 1)) : RangeHas n pred a b ∧ pred ⟨b, hb⟩ := by
  constructor
  · intro _ _ _
    apply h; all_goals omega
  · apply h; all_goals simp only; omega


protected theorem prepend (hr : pred ⟨a, ha⟩) (hrs : RangeHas n pred (a + 1) b) : RangeHas n pred a b := fun k_ h1 h2 =>
  (Nat.eq_or_lt_of_le h1).elim
    ( · |> Fin.eq_of_val_eq (i := ⟨a,_⟩) |> (· ▸ hr))
    (hrs k_ · h2)

protected theorem unprepend (hab : a < b) (h : RangeHas n pred a b) : pred ⟨a, ha⟩ ∧ RangeHas n pred (a + 1) b := by
  constructor
  · apply h; all_goals simp only; omega
  · intro _ _ _
    apply h; all_goals omega
