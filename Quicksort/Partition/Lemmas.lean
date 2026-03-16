import Quicksort.Partition.Hoare.Lemmas
import Quicksort.Partition.Lomuto.Lemmas

import Quicksort.Partition.Basic

open Vector

namespace Partition
variable (lt : α → α → Bool := by exact (· < ·))

-- private class LT_Asymm (α : Type u) (lt : α → α → Bool := by exact (· < ·)) : Prop where
-- private class LE_Trans (α : Type u) (lt : α → α → Bool := by exact (· < ·)) : Prop where

-- -- variable (le_trans : ∀ {x y z : α}, ¬lt y x → ¬lt z y → ¬lt z x)
-- -- variable (lt_asymm : ∀ {x y : α}, lt x y → ¬lt y x)

class StrictOrder (α : Type u) (lt : α → α → Bool)  : Prop where
  lt_asymm : ∀ {x y : α}, lt x y → ¬lt y x
  le_trans : ∀ {x y z : α}, ¬lt y x → ¬lt z y → ¬lt z x

export StrictOrder (lt_asymm le_trans)


class LawfulScheme (part : Partition.Scheme α) : Prop where
  partitionBounds : (part (lt := lt) as left right hlr hr).val.j' < (part (lt := lt) as left right hlr hr).val.i'
  permStabilizing : PermStabilizing' left right (part (lt := lt) as left right hlr hr).val.arr' as
  sorting [StrictOrder α lt] (as : Vector α n) (hlr : left < right) (hr : right < n) : ∃ (pivot : α), IsPartitioned (lt := lt) left right pivot (part (lt := lt) as left right hlr hr).val

instance instLawfulHoareScheme : LawfulScheme (lt := lt) (α := α) (part := @hoare α) where
  partitionBounds := hoare.partition_bounds (lt := lt)
  permStabilizing := hoare.permStabilizing (lt := lt)
  sorting _ _ _ := hoare.sorted lt_asymm le_trans (lt := lt)

instance instLawfulLomutoScheme : LawfulScheme (lt := lt) (α := α) (part := @lomuto α) where
  partitionBounds := lomuto.partition_bounds (lt := lt)
  permStabilizing := lomuto.permStabilizing (lt := lt)
  sorting _ _ _ := lomuto.sorted lt_asymm (lt := lt)

instance  instLawfulDefaultScheme : LawfulScheme (lt := lt) (α := α) (@default _ _) := by
  simp only [default]; first
  | exact instLawfulHoareScheme (lt := lt)
  | exact instLawfulLomutoScheme (lt := lt)
