
import Quicksort.Partition.Hoare.Basic
import Quicksort.Partition.Hoare.Eager.Lemmas
import Quicksort.Partition.Hoare.Classic.Lemmas
import Quicksort.Partition.Init.Lemmas

open Vector

namespace Partition
variable [Ord α]

protected theorem hoare.partition_bounds {arr : Vector α n} {left : Nat} {right : Nat} {hlr : left < right} {hr : right < n} : (Partition.hoare arr left right hlr hr).val.j' < (Partition.hoare arr left right hlr hr).val.i' := by
  unfold Partition.hoare; simp [*]; split
  · apply hoare.classic.loop.partition_bounds
  · apply hoare.eager.partition_bounds; assumption

protected theorem hoare.permStabilizing {arr : Vector α n} {left : Nat} {right : Nat} {hlr : left < right} {hr : right < n} : PermStabilizing' left right (Partition.hoare arr left right hlr hr).val.arr' arr := by
  unfold Partition.hoare; simp [*]; split
  · apply PermStabilizing'.trans
    · apply PermStabilizing'.mono hoare.classic.loop.permStabilizing <;> omega
    · apply PermStabilizing'.trans
      apply PermStabilizing'.trans
      all_goals apply maybeSwap_permStabilizing
      all_goals simp only; omega
  · apply hoare.eager.permStabilizing; assumption

protected theorem hoare.sorted [Std.TransOrd α] {arr : Vector α n} {left : Nat} {right : Nat} {hlr : left < right} {hr : right < n} : ∃ (pivot : α), IsPartitioned left right pivot (Partition.hoare arr left right hlr hr).val := by
  unfold Partition.hoare; simp [*]; split
  · apply hoare.classic.sorted <;> grind
  · apply hoare.eager.sorted <;> grind
