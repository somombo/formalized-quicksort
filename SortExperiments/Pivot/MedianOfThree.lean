module
import Quicksort.Init.Ord

public import SortExperiments.Pivot.Init

@[inline]
def Pivot.maybeSwap [Ord α] (as : Vector α n) (low high : Fin n) : Vector α n :=
  if compare as[high] as[low] |>.isLT then
    -- (dbgTraceIfShared "Pivot.maybeSwap `as` is shared!" as).swap low high
    as.swap low high
  else
    as

@[inline]
public def Pivot.median_of_three [Ord α] (arr : Vector α n) (left : Nat)  (right : Nat) (hlr : left < right) (hr : right < n) : Pivot α n:=
  have hl : left < n := by omega

  let mid := left + ((right - left + 1)/2)
  have hm : mid < n := by omega
  let arr_ := arr
    |> (maybeSwap · ⟨left, hl⟩ ⟨mid, hm⟩)
    |> (maybeSwap · ⟨left, hl⟩ ⟨right, hr⟩)
    |> (maybeSwap · ⟨mid, hm⟩ ⟨right, hr⟩)

  let pivot := arr_[mid]
  ⟨pivot, arr_⟩






theorem Pivot.maybeSwap_sorted [Ord α]  (lt_asymm : ∀ {x y : α}, (compare x y |>.isLT) → ¬(compare y x |>.isLT))  (as : Vector α n) (low high : Nat) (hlh : low ≤ high) (hn : high < n) : ¬ (compare (maybeSwap as ⟨low, by omega⟩ ⟨high, by omega⟩)[high] (maybeSwap as ⟨low, by omega⟩ ⟨high, by omega⟩)[low] |>.isLT) := by
  unfold maybeSwap; split
  · next h =>
      grind [as.getElem_swap_right, as.getElem_swap_left]
  · assumption


-- (halgep : arr[left] ≤ pivot)  (harltp : pivot ≤ arr[right])
-- (halgep : ∃ (j_ : Fin n) (_ : j_ ≤ righXt), arr[j_] ≤ pivot)  (harltp : ∃ (i_ : Fin n) (_ : left ≤ i_), pivot ≤ arr[i_])
open Ord in
public theorem Pivot.median_of_three_sorted [Ord α]
    (not_lt : ∀ {x y : α}, ¬(compare y x |>.isLT) ↔ (compare x y |>.isLE) := by grind)
    (le_trans : ∀ {x y z : α}, (compare x y).isLE → (compare y z).isLE → (compare x z).isLE := by grind)
    {arr : Vector α n} {left right: Nat} (hlr : left < right) (hr : right < n) :
    let ⟨pivot, arr_⟩ := median_of_three arr left right hlr hr;
    ¬(compare pivot arr_[left] |>.isLT) ∧ ¬(compare arr_[right] pivot |>.isLT) := by
  have lt_asymm : ∀ {x y : α}, (compare x y |>.isLT) → ¬(compare y x |>.isLT) := by grind
  have le_trans' : ∀ {x y z : α}, ¬(compare y x |>.isLT) → ¬(compare z y |>.isLT) → ¬(compare z x |>.isLT) := by grind

  let mid := left + ((right - left + 1)/2)

  have _ : left < n := by omega
  have _ : mid < n := by omega

  have hlm : left ≤ mid := by omega
  have hmr : mid ≤ right := by omega
  let arr1 : Vector α n := maybeSwap arr ⟨left, by omega⟩ ⟨mid, by omega⟩
  let arr2 : Vector α n := maybeSwap arr1 ⟨left, by omega⟩ ⟨right, by omega⟩
  let arr_ : Vector α n := maybeSwap arr2 ⟨mid, by omega⟩ ⟨right, by omega⟩

  change ¬(compare arr_[mid] arr_[left] |>.isLT) ∧ ¬(compare arr_[right] arr_[mid] |>.isLT)

  have hh1 : ¬(compare arr1[mid] arr1[left] |>.isLT) := maybeSwap_sorted lt_asymm arr left mid (by omega) (by omega)
  have hh2 : ¬(compare arr2[right] arr2[left] |>.isLT) := maybeSwap_sorted lt_asymm arr1 left right (by omega) (by omega)
  have hh_ : ¬(compare arr_[right] arr_[mid] |>.isLT) := maybeSwap_sorted lt_asymm arr2 mid right (by omega) (by omega)

  suffices ¬(compare arr_[mid] arr_[left] |>.isLT) from ⟨this, hh_⟩

  if hleqm : left = mid then
    simp only [hleqm]
    exact lt_irrefl lt_asymm arr_[mid]
  else
    have hlneqr : left ≠ right := by omega
    simp only [arr_]
    unfold maybeSwap
    split
    · have : (arr2.swap mid right)[left] = _ :=
        arr2.getElem_swap_of_ne hleqm hlneqr
      grind [arr2.getElem_swap_left]
    · if hmeqr : mid = right then
        simp only [hmeqr]
        exact hh2
      else
        simp only [arr2]
        unfold maybeSwap
        split

        · have : (arr1.swap left right)[mid] = _ :=
            arr1.getElem_swap_of_ne (Ne.symm hleqm) hmeqr
          grind [arr1.getElem_swap_left]
        · assumption
