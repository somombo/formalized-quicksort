import Quicksort.Partition.Basic



@[inline]
def qs [Ord α] (arr : Array α) (left : Nat := 0) (right : Nat := arr.size - 1) (part : Partition.Scheme α := @default _ _) : Array α :=
  let rec @[specialize]
  strict {n : Nat} (as : Batteries.Vector α n) (left : Nat := 0) (right : Nat := n - 1) (hsize' : right ≤ n - 1) : Batteries.Vector α n :=
    if hlr : left < right then
      let ⟨⟨as', j', i'⟩, (_ : _ < i'), (_ : j' < _ )⟩ := part as left right hlr (by omega)
      let as := qs.strict as' left j' (by omega)
      let as := qs.strict as i' right (by omega)
      as
    else
      as
    termination_by right - left

  let right' : Nat := if right ≤ arr.size - 1 then right else
    have := Inhabited.mk (arr.size - 1)
    panic! "index out of bounds"

  have : right' ≤ arr.size - 1 := by
    simp [right']; split <;> simp [panicWithPosWithDecl, panic, panicCore, *]

  qs.strict ⟨arr, rfl⟩ left right' this |>.1
