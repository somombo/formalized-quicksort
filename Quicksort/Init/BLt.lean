module

public class BLt (α : Type u) where
  blt : α → α → Bool

export BLt (blt)

namespace BLt
@[expose, inline]
public instance (priority := 900) [LT α] [DecidableLT α] : BLt α := ⟨(· < ·)⟩
@[expose, inline]
public instance (priority := low) instBLtOfOrd [Ord α] : BLt α := ⟨(compare · · |>.isLT)⟩

variable [BLt α]

@[expose, inline]
public instance {α : Type} : Coe (α → α → Bool) (BLt α) where
  coe f := ⟨f⟩

-- public instance {α : Type} : CoeFun (BLt α) (fun _ => α → α → Bool) where
--   coe r := r.blt


example : BLt Nat := ⟨(· < ·)⟩


@[expose, inline]
public abbrev lt := @blt

@[expose, inline]
public abbrev le (x y : α) := ¬ lt y x

@[expose, inline]
public abbrev eq (x y : α) := ¬ lt y x ∧ ¬ lt x y

@[grind]
public class IsStrictWeakOrder (α : Type u) [BLt α] : Prop where
  lt_asymm : ∀ {x y : α}, blt x y → ¬blt y x
  le_trans' : ∀ {x y z : α}, ¬blt y x → ¬blt z y → ¬blt z x

export IsStrictWeakOrder (lt_asymm le_trans')


public theorem lt_irrefl (lt_asymm : ∀ {x y : α}, lt x y → ¬lt y x) : ∀ (x : α), ¬lt x x := fun _ h => (lt_asymm h) h

@[expose, inline, implicit_reducible]
public def toLT [BLt α] : LT α where
  lt a b := blt a b = true


@[expose, implicit_reducible]
public def toDecidableLT [BLt α] : @DecidableLT α toLT := by
  intro a b
  show Decidable (blt a b = true)
  infer_instance
end BLt

export BLt (lt le eq lt_irrefl)




@[expose, inline]
public instance instOrdOfBLt [BLt α] : Ord α where
  compare a b :=
    if blt a b then .lt
    else if blt b a then .gt
    else .eq


namespace Std
variable [Ord α]

@[grind ·]
theorem OrientedOrd.isLT_asymm [OrientedOrd α] : ∀ {x y : α}, (compare x y).isLT → ¬(compare y x).isLT := by
  intro x y
  have _ : compare y x = (compare x y).swap := OrientedOrd.eq_swap
  cases _ :  compare x y <;> simp_all



@[simp, grind .]
theorem OrientedOrd.isLE_iff_not_LT [OrientedOrd α] : ∀ {x y : α}, ¬(compare y x |>.isLT) ↔  (compare x y |>.isLE) := by
  intro x y
  cases h : compare y x <;> simp [h, OrientedOrd.eq_swap]


@[grind ·]
theorem TransOrd.isLE_trans' [TransOrd α] :
    ∀ {x y z : α}, ¬(compare y x |>.isLT) → ¬(compare z y |>.isLT) → ¬(compare z x |>.isLT) := by
  grind [TransOrd.isLE_trans]

end Std

namespace Ord
@[inline]
private abbrev lt [Ord α] (x y : α) := compare x y |>.isLT

public instance (priority := low) [Ord α] [Std.TransOrd α] : BLt.IsStrictWeakOrder α where
  lt_asymm : ∀ {x y : α}, lt x y → ¬lt y x := by grind
  le_trans' : ∀ {x y z : α}, ¬lt y x → ¬lt z y → ¬lt z x := by grind
end Ord


namespace LT
public instance [LT α] [DecidableLT α]  [LE α] [Std.LawfulOrderLT α] [Std.IsLinearPreorder α] : BLt.IsStrictWeakOrder α  where
  lt_asymm := by
    intro x y h1 h2
    simp only [blt] at *
    grind
  le_trans' := by
    intro x y z h1 h2 h3
    simp only [blt] at *
    grind
end LT
