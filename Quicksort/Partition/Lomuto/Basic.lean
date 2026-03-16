import Quicksort.Partition.Init.Basic

open Vector

@[inline]
def Partition.lomuto {n : Nat} (arr : Vector α n) (left : Nat)  (right : Nat) (hlr : left < right) (hr : right < n) (lt : α → α → Bool := by exact (· < ·)) : {x : Partition α n // (left < x.i') ∧ (x.j' < right)} :=
  let mid := left + ((right - left)/2)
  let arr_ := arr
    |> (maybeSwap (lt := lt) · ⟨left, by omega⟩ ⟨mid, by omega⟩)
    |> (maybeSwap (lt := lt) · ⟨left, by omega⟩ ⟨right, by omega⟩)
    |> (maybeSwap (lt := lt) · ⟨right, by omega⟩ ⟨mid, by omega⟩)
  have pivot := arr_[right]

  let rec @[specialize] loop (as : Vector α n) (i j : Nat) (hli : left ≤ i) (hij :  i ≤ j  ) (hjr : j ≤ right) : { x : Partition α n // left < x.i' ∧ x.j' < right } :=
    if _ : j < right then
      if lt as[j] pivot then
        loop (as.swap i j) (i + 1) (j + 1) (by omega) (by omega) (by omega)
      else
        loop as i (j + 1) hli (by omega) (by omega)
    else
      ⟨⟨as.swap i right, i - 1, i + 1⟩, by simp only; omega, by simp only; omega⟩
  -- termination_by right - j
  loop arr_ left left (by omega) (by omega) (by omega)
