
import Quicksort.Init.Ord

#check Array.insertionSort


@[inline]
def Array.insertionSort_left_right [Ord α]  (xs : Array α) -- (lt : α → α → Bool := by exact (· < ·))
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
def Array.insertionSort_without_fuel [Ord α]  (xs : Array α)  -- (lt : α → α → Bool := by exact (· < ·))
    /- (_left := 0) (right := n - 1) (_hr : right ≤ n - 1 := by omega) -/ : Array α :=
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
def Vector.insertionSort [Ord α] {n : Nat} (xs : Vector α n) -- (lt : α → α → Bool := by exact (· < ·))
    (left := 0) (right := n - 1) (hr : right ≤ n - 1 := by omega) : Vector α n :=
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
def Vector.insertionSort' {n : Nat} (xs : Vector α n)
    (left := 0) (right := n - 1) (hr : right ≤ n - 1 := by omega)
    [Ord α] : Vector α n :=
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
      if compare xs[j] xs[j'] |>.isLT then
        swapLoop (xs.swap j j') j' (by omega)
      else
        xs
    else
      xs
