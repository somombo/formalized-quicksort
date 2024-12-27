import Quicksort.Partition.Hoare.Lemmas
import Quicksort.Partition.Lomuto.Lemmas

import Quicksort.Partition.Basic

open Batteries Vector

namespace Partition
variable [Ord α]

-- private class LT_Asymm (α : Type u) [Ord α] : Prop where
-- private class LE_Trans (α : Type u) [Ord α] : Prop where

-- -- variable (le_trans : ∀ {x y z : α}, ¬lt y x → ¬lt z y → ¬lt z x)
-- -- variable (lt_asymm : ∀ {x y : α}, lt x y → ¬lt y x)

class StrictOrder (α : Type u) [Ord α]  : Prop where
  lt_asymm : ∀ {x y : α}, lt x y → ¬lt y x
  le_trans : ∀ {x y z : α}, ¬lt y x → ¬lt z y → ¬lt z x

export StrictOrder (lt_asymm le_trans)


class LawfulScheme (part : Partition.Scheme α) : Prop where
  partitionBounds : (part as left right hlr hr).val.j' < (part as left right hlr hr).val.i'
  permStabilizing : PermStabilizing' left right (part as left right hlr hr).val.arr' as
  sorting [StrictOrder α] (as : Vector α n) (hlr : left < right) (hr : right < n) : ∃ (pivot : α), IsPartitioned left right pivot (part as left right hlr hr).val

instance instLawfulHoareScheme : LawfulScheme (α := α) hoare where
  partitionBounds := hoare.partition_bounds
  permStabilizing := hoare.permStabilizing
  sorting _ _ _ := hoare.sorted lt_asymm le_trans

instance instLawfulLomutoScheme : LawfulScheme (α := α) lomuto where
  partitionBounds := lomuto.partition_bounds
  permStabilizing := lomuto.permStabilizing
  sorting _ _ _ := lomuto.sorted lt_asymm

instance  instLawfulDefaultScheme : LawfulScheme (α := α) (@default _ _) := by
  simp only [default]; first
  | exact instLawfulHoareScheme
  | exact instLawfulLomutoScheme
