module
variable [Ord α]

namespace Std


@[simp]
public theorem not_lt_iff_eq_swap :
    (∀ {x y : α}, ¬(compare y x |>.isLT) ↔ (compare x y |>.isLE)) ↔
    (∀ {x y : α}, compare x y = (compare y x).swap) := by
  constructor
  · intro not_lt
    intro x y
    have _ := not_lt (x := x) (y := y)
    have _ := not_lt (x := y) (y := x)
    cases h : compare x y <;> cases _ : compare y x <;>
      simp_all

  · intro eq_swap
    intro x y
    cases h : compare y x <;> simp [h, eq_swap]

@[grind =]
public theorem eq_swap_of_not_lt :
    (∀ {x y : α}, ¬(compare y x |>.isLT) ↔ (compare x y |>.isLE)) →
    (∀ {x y : α}, compare x y = (compare y x).swap) := not_lt_iff_eq_swap.1


@[simp, grind .]
public theorem OrientedOrd.isLE_iff_not_LT [OrientedOrd α] : ∀ {x y : α}, ¬(compare y x |>.isLT) ↔  (compare x y |>.isLE) :=
  not_lt_iff_eq_swap.2 OrientedOrd.eq_swap

@[grind ·]
public theorem OrientedOrd.isLT_asymm' (eq_swap : ∀ {x y : α}, compare x y = (compare y x).swap) : ∀ {x y : α}, (compare x y).isLT → ¬(compare y x).isLT := by
  intro x y
  cases h :  compare x y <;> simp [h, eq_swap]




@[grind ·]
public theorem OrientedOrd.isLT_asymm [OrientedOrd α] : ∀ {x y : α}, (compare x y).isLT → ¬(compare y x).isLT := by
  intro x y
  have _ : compare y x = (compare x y).swap := OrientedOrd.eq_swap
  cases _ :  compare x y <;> simp_all





public instance instTransOrdOfnot_lt_le_trans
    (not_lt : ∀ {x y : α}, ¬(compare y x |>.isLT) ↔ (compare x y |>.isLE) := by grind)
    (le_trans : ∀ {x y z : α}, (compare x y).isLE → (compare y z).isLE → (compare x z).isLE := by grind) :
    TransOrd α where
  isLE_trans := le_trans
  eq_swap := not_lt_iff_eq_swap.1 not_lt



attribute [grind .] TransOrd.isLE_trans

@[grind ·]
public theorem TransOrd.isLE_trans' [TransOrd α] :
    ∀ {x y z : α}, ¬(compare y x |>.isLT) → ¬(compare z y |>.isLT) → ¬(compare z x |>.isLT) := by
  grind

end Std


@[expose, inline]
public abbrev lt (x y : α) := compare x y |>.isLT
@[expose, inline]
public abbrev le (x y : α) := compare x y |>.isLE
@[expose, inline]
public abbrev eq (x y : α) := compare x y |>.isEq



namespace Ord
open Std
-- aliases of the above
public theorem not_lt [OrientedOrd α] : ∀ {x y : α}, ¬lt y x ↔ le x y := OrientedOrd.isLE_iff_not_LT
public theorem le_trans [TransOrd α] : ∀ {x y z : α}, le x y → le y z → le x z := TransOrd.isLE_trans
public theorem lt_asymm [OrientedOrd α] : ∀ {x y : α}, lt x y → ¬lt y x := OrientedOrd.isLT_asymm
public theorem le_trans' [TransOrd α] : ∀ {x y z : α}, ¬lt y x → ¬lt z y → ¬lt z x := TransOrd.isLE_trans'

end Ord
public theorem Ord.lt_irrefl (lt_asymm : ∀ {x y : α}, lt x y → ¬lt y x) : ∀ (x : α), ¬lt x x := fun _ h => (lt_asymm h) h



namespace examples
private scoped instance : Ord (Bool × String) := lexOrd
example : ∀ {x y z : Bool × String}, le x y → le y z → le x z := by grind
example : ∀ {x y : UInt32}, lt x y → ¬lt y x := by grind
example : ∀ {x y z : UInt32}, ¬lt y x → ¬lt z y → ¬lt z x := by grind

example : ∀ {x y : Int}, lt x y → ¬lt y x := by grind
example : ∀ {x y z : Int}, ¬lt y x → ¬lt z y → ¬lt z x := by grind
end examples


@[macro_inline]
public instance ltBoolToOrd (lt : α → α → Bool) : Ord α where
  compare a b :=
    if lt a b then .lt
    else if lt b a then .gt
    else .eq;
