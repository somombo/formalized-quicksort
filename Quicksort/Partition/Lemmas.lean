import Quicksort.Partition.Hoare.Lemmas
import Quicksort.Partition.Lomuto.Lemmas

import Quicksort.Partition.Basic

open Vector

namespace Partition
variable [Ord α]

class LawfulScheme (part : Partition.Scheme α) : Prop where
  partitionBounds : (part as left right hlr hr).val.j' < (part as left right hlr hr).val.i'
  permStabilizing : PermStabilizing' left right (part as left right hlr hr).val.arr' as
  sorting [Std.TransOrd α] (as : Vector α n) (hlr : left < right) (hr : right < n) : ∃ (pivot : α), IsPartitioned left right pivot (part as left right hlr hr).val

open Ord
instance instLawfulHoareScheme : LawfulScheme (α := α) hoare where
  partitionBounds := hoare.partition_bounds
  permStabilizing := hoare.permStabilizing
  sorting _ _ _ := hoare.sorted

instance instLawfulLomutoScheme : LawfulScheme (α := α) lomuto where
  partitionBounds := lomuto.partition_bounds
  permStabilizing := lomuto.permStabilizing
  sorting _ _ _ := lomuto.sorted lt_asymm

instance  instLawfulDefaultScheme : LawfulScheme (α := α) (@default _ _) := by
  simp only [default]; first
  | exact instLawfulHoareScheme
  | exact instLawfulLomutoScheme
