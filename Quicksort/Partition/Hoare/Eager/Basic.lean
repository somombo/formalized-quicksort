import Quicksort.Partition.Init.Basic

open Batteries Vector

@[inline]
def Partition.hoare.eager [Ord α] {n : Nat} (arr : Vector α n) (left : Nat)  (right : Nat) (hlr : left < right) (hr : right < n) : {x : Partition α n // (left < x.i') ∧ (x.j' < right)} :=
  let mid := left + ((right - left)/2)
  let arr_ := arr
    |> (maybeSwap · ⟨left, by omega⟩ ⟨mid, by omega⟩)
    |> (maybeSwap · ⟨left, by omega⟩ ⟨right, by omega⟩)
    |> (maybeSwap · ⟨mid, by omega⟩ ⟨right, by omega⟩)
  have pivot := arr_[mid]

  let rec @[specialize] loop (arr : Vector α n) (i j : Nat) (hli : left < i) (hij : i ≤ j + 1) (hjr : j < right) : { x : Partition α n // left < x.i' ∧ x.j' < right } :=
    if _ : j < i then
      ⟨⟨arr, j, i⟩, ⟨hli, hjr⟩⟩
    else
      if (lt arr[i] pivot)  then
        loop arr (i + 1) j (by omega) (by omega) (by omega)
      else if (lt pivot arr[j]) then
        loop arr i (j - 1) (by omega) (by omega) (by omega)
      else
        if hlt : i < j then
          loop (arr.swap ⟨i, by omega⟩ ⟨j, by omega⟩) (i + 1) (j - 1) (by omega) (by omega) (by omega)
        else
          ⟨⟨arr, j - 1, i + 1⟩, ⟨(by omega : _ < i + 1), (by omega : j - 1 < _)⟩⟩
  -- termination_by j + 1 - i

  loop arr_ (left + 1) (right - 1) (by omega) (by omega) (by omega)
