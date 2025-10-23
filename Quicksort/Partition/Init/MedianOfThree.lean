import Quicksort.Partition.Init.Basic

open Vector

namespace Partition

variable [Ord α]
variable (lt_asymm : ∀ {x y : α}, lt x y → ¬lt y x)

include lt_asymm in
private theorem lt_irrefl : ∀ (x : α), ¬lt x x :=
  fun _ h => (lt_asymm h) h

include lt_asymm in
theorem maybeSwap_sorted (as : Vector α n) (low high : Nat) (hlh : low ≤ high) (hn : high < n) : ¬ (lt (maybeSwap as ⟨low, by omega⟩ ⟨high, by omega⟩)[high] (maybeSwap as ⟨low, by omega⟩ ⟨high, by omega⟩)[low]) := by
  unfold maybeSwap; split
  · next h =>
      simp only [as.getElem_swap_right, as.getElem_swap_left]
      exact lt_asymm h
  · assumption

variable (le_trans : ∀ {x y z : α}, ¬lt y x → ¬lt z y → ¬lt z x)
-- set_option trace.profiler true in
include lt_asymm in
include le_trans in
theorem median_of_three_sorted {arr : Vector α n} {left mid right: Nat} (hlm : left ≤ mid) (hmr : mid ≤ right) (hr : right < n) :
  let arr_ := arr
    |> (maybeSwap · ⟨left, by omega⟩ ⟨mid, by omega⟩)
    |> (maybeSwap · ⟨left, by omega⟩ ⟨right, by omega⟩)
    |> (maybeSwap · ⟨mid, by omega⟩ ⟨right, by omega⟩)

  ¬lt arr_[mid] arr_[left] ∧ ¬lt arr_[right] arr_[mid]
  :=
  have _ : left < n := by omega
  have _ : mid < n := by omega

  let arr1 : Vector α n := maybeSwap arr ⟨left, by omega⟩ ⟨mid, by omega⟩
  let arr2 : Vector α n := maybeSwap arr1 ⟨left, by omega⟩ ⟨right, by omega⟩
  let arr_ : Vector α n := maybeSwap arr2 ⟨mid, by omega⟩ ⟨right, by omega⟩

  have hh1 : ¬lt arr1[mid] arr1[left] := maybeSwap_sorted lt_asymm arr left mid (by omega) (by omega)
  have hh2 : ¬lt arr2[right] arr2[left] := maybeSwap_sorted lt_asymm arr1 left right (by omega) (by omega)
  have hh_ : ¬lt arr_[right] arr_[mid] := maybeSwap_sorted lt_asymm arr2 mid right (by omega) (by omega)

  suffices ¬lt arr_[mid] arr_[left] from ⟨this, hh_⟩

  if hleqm : left = mid then by
    simp only [hleqm]
    exact lt_irrefl lt_asymm arr_[mid]
  else by
    have hlneqr : left ≠ right := by omega
    simp only [arr_]
    unfold maybeSwap
    split
    · have : (arr2.swap mid right)[left] = _ :=
        arr2.getElem_swap_of_ne hleqm hlneqr
      simp only [this, arr2.getElem_swap_left]
      assumption
    · exact
      if hmeqr : mid = right then by
        simp only [hmeqr]
        exact hh2
      else by
        simp only [arr2]
        unfold maybeSwap
        split

        · have : (arr1.swap left right)[mid] = _ :=
            arr1.getElem_swap_of_ne (Ne.symm hleqm) hmeqr
          simp only [this, arr1.getElem_swap_left]
          refine le_trans (lt_asymm ?_) hh1
          assumption
        · assumption
