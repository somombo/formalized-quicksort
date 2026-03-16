
import Quicksort.Partition.Basic
import Quicksort.Partition.Yaroslavskiy.Basic
import Quicksort.Partition.Dutch.Basic

@[inline]
def Array.insertionSort_left_right (xs : Array α) (lt : α → α → Bool := by exact (· < ·))
    : Array α :=
  traverse xs.toVector 1 (left := 0) (right := xs.size - 1) (hr := by omega)  |>.toArray

where
  @[specialize]
  traverse {n : Nat} (xs : Vector α n) (i : Nat) (left : Nat) (right : Nat) (hr : right ≤ n - 1)  : Vector α n :=
    if h : i ≤ right then
      traverse (swapLoop xs i (by omega) left) (i+1) left right hr
    else
      xs
    termination_by right + 1 - i

  @[specialize]
  swapLoop  {n : Nat} (xs : Vector α n) (j : Nat)  (h : j ≤ n - 1) (left : Nat):  Vector α n :=
    if _ : left < j then
      let j' := j - 1
      if lt xs[j] xs[j'] then
        swapLoop  (xs.swap j j') j' (by omega) left
      else
        xs
    else
      xs


@[inline]
def Array.insertionSort_without_fuel (xs : Array α)
    /- (_left := 0) (right := n - 1) (_hr : right ≤ n - 1 := by omega) -/
    (lt : α → α → Bool := by exact (· < ·)) : Array α :=
  traverse xs.toVector (0 + 1) |>.toArray
where
  @[specialize]
  traverse {n : Nat} (xs : Vector α n) (i : Nat)  : Vector α n :=
    if h : i ≤ (n - 1) then
      traverse (swapLoop xs i (by omega)) (i+1)
    else
      xs
    termination_by (n - 1) + 1 - i

  @[specialize]
  swapLoop {n : Nat} (xs : Vector α n) (j : Nat) (h : j ≤ n - 1) :  Vector α n :=
    if _ : 0 < j then
      let j' := j - 1
      if lt xs[j] xs[j'] then
        swapLoop (xs.swap j j') j' (by omega)
      else
        xs
    else
      xs

@[inline]
def Vector.insertionSort {n : Nat} (xs : Vector α n)
    (left := 0) (right := n - 1) (hr : right ≤ n - 1 := by omega)
    (lt : α → α → Bool := by exact (· < ·)) : Vector α n :=
  traverse xs (left + 1)
where
  @[specialize]
  traverse (xs : Vector α n) (i : Nat)  : Vector α n :=
    if h : i ≤ right then
      traverse (swapLoop xs i (by omega)) (i+1)
    else
      xs
    termination_by right + 1 - i

  @[specialize]
  swapLoop (xs : Vector α n) (j : Nat) (h : j ≤ n - 1) :  Vector α n :=
    if _ : left < j then
      let j' := j - 1
      if lt xs[j] xs[j'] then
        swapLoop (xs.swap j j') j' (by omega)
      else
        xs
    else
      xs

@[inline]
def qs_adapt (arr : Array α) (left : Nat := 0) (right : Nat := arr.size - 1) (M := 0) (part : Partition.Scheme α ) (lt : α → α → Bool := by exact (· < ·)) : Array α :=
  -- let part := @Partition.dutch α
  let rec @[specialize]
  strict {n : Nat} (as : Vector α n) (left : Nat := 0) (right : Nat := n - 1) (hsize' : right ≤ n - 1) : Vector α n :=
    if hlr : left + M < right then
      let ⟨⟨as', j', i'⟩, (_ : _ < i'), (_ : j' < _ )⟩ := part (lt := lt) as left right (by omega) (by omega)
      let as := qs_adapt.strict as' left j' (by omega)
      let as := qs_adapt.strict as i' right (by omega)
      as
    else
      as.insertionSort (lt := lt) left right
    termination_by right - left

  let right' : Nat := if right ≤ arr.size - 1 then right else
    have := Inhabited.mk (arr.size - 1)
    panic! "index out of bounds"

  have : right' ≤ arr.size - 1 := by
    simp [right']; split <;> simp [panicWithPosWithDecl, panic, panicCore, *]

  qs_adapt.strict ⟨arr, rfl⟩ left right' this |>.1
