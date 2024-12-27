import Quicksort.Partition.Init.Basic

open Batteries Vector

@[inline] def Partition.lomuto [Ord α] {n : Nat} (arr : Vector α n) (left : Nat)  (right : Nat) (hlr : left < right) (hr : right < n) : {x : Partition α n // (left < x.i') ∧ (x.j' < right)} :=
  let mid := left + ((right - left)/2)
  let arr_ := arr
    |> (maybeSwap · ⟨left, by omega⟩ ⟨mid, by omega⟩)
    |> (maybeSwap · ⟨left, by omega⟩ ⟨right, by omega⟩)
    |> (maybeSwap · ⟨right, by omega⟩ ⟨mid, by omega⟩)
  have pivot := arr_[right]

  let rec @[specialize] loop (as : Vector α n) (i j : Nat) (hli : left ≤ i) (hij :  i ≤ j  ) (hjr : j ≤ right) : { x : Partition α n // left < x.i' ∧ x.j' < right } :=
    let i_fin : Fin n := ⟨i, by omega⟩

    if _ : j < right then
      if lt as[j] pivot then
        loop (as.swap i_fin ⟨j, by omega⟩) (i + 1) (j + 1) (by omega) (by omega) (by omega)
      else
        loop as i (j + 1) hli (by omega) (by omega)
    else
      ⟨⟨as.swap i_fin ⟨right, hr⟩, i - 1, i + 1⟩, by simp only; omega, by simp only; omega⟩
  -- termination_by right - j
  loop arr_ left left (by omega) (by omega) (by omega)
