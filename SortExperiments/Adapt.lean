
import Quicksort.Partition.Basic
import SortExperiments.InsertionSort




@[inline]
def qs_adapt [Ord α] (arr : Array α) (left : Nat := 0) (right : Nat := arr.size - 1) (M := 0) (part : Partition.Scheme α := @default _ _) : Array α :=
  -- let part := @Partition.dutch α
  let rec @[specialize]
  strict {n : Nat} (as : Vector α n) (left : Nat := 0) (right : Nat := n - 1) (hsize' : right ≤ n - 1) : Vector α n :=
    if hlr : left + M < right then
      let ⟨⟨as', j', i'⟩, (_ : _ < i'), (_ : j' < _ )⟩ := part as left right (by omega) (by omega)
      let as := qs_adapt.strict as' left j' (by omega)
      let as := qs_adapt.strict as i' right (by omega)
      as
    else
      as.insertionSort left right
    termination_by right - left

  let right' : Nat := if right ≤ arr.size - 1 then right else
    have := Inhabited.mk (arr.size - 1)
    panic! "index out of bounds"

  have : right' ≤ arr.size - 1 := by
    simp [right']; split <;> simp [panicWithPosWithDecl, panic, panicCore, *]

  qs_adapt.strict ⟨arr, rfl⟩ left right' this |>.1
