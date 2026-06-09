module
public import Quicksort.Init.Ord

public import SortExperiments.Pivot.Init

@[inline]
def Pivot.maybeSwap [Ord α] (as : Vector α n) (low high : Fin n) : Vector α n :=
  if lt as[high] as[low] then
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






theorem Pivot.maybeSwap_sorted [Ord α]  (lt_asymm : ∀ {x y : α}, lt x y → ¬lt y x)  (as : Vector α n) (low high : Nat) (hlh : low ≤ high) (hn : high < n) : ¬ (lt (maybeSwap as ⟨low, by omega⟩ ⟨high, by omega⟩)[high] (maybeSwap as ⟨low, by omega⟩ ⟨high, by omega⟩)[low]) := by
  unfold maybeSwap; split
  · next h =>
      grind [as.getElem_swap_right, as.getElem_swap_left]
  · assumption


-- (halgep : arr[left] ≤ pivot)  (harltp : pivot ≤ arr[right])
-- (halgep : ∃ (j_ : Fin n) (_ : j_ ≤ righXt), arr[j_] ≤ pivot)  (harltp : ∃ (i_ : Fin n) (_ : left ≤ i_), pivot ≤ arr[i_])
open Ord in
public theorem Pivot.median_of_three_sorted [Ord α] [Std.TransOrd α]
    {arr : Vector α n} {left right: Nat} (hlr : left < right) (hr : right < n) :
    let ⟨pivot, arr_⟩ := median_of_three arr left right hlr hr;
    ¬(lt pivot arr_[left]) ∧ ¬(lt arr_[right] pivot) := by
  have lt_asymm : ∀ {x y : α}, (lt x y) → ¬(lt y x) := by grind
  have le_trans' : ∀ {x y z : α}, ¬(lt y x) → ¬(lt z y) → ¬(lt z x) := by grind

  let mid := left + ((right - left + 1)/2)

  have _ : left < n := by omega
  have _ : mid < n := by omega

  have hlm : left ≤ mid := by omega
  have hmr : mid ≤ right := by omega
  let arr1 : Vector α n := maybeSwap arr ⟨left, by omega⟩ ⟨mid, by omega⟩
  let arr2 : Vector α n := maybeSwap arr1 ⟨left, by omega⟩ ⟨right, by omega⟩
  let arr_ : Vector α n := maybeSwap arr2 ⟨mid, by omega⟩ ⟨right, by omega⟩

  change ¬(lt arr_[mid] arr_[left]) ∧ ¬(lt arr_[right] arr_[mid])

  have hh1 : ¬(lt arr1[mid] arr1[left]) := maybeSwap_sorted lt_asymm arr left mid (by omega) (by omega)
  have hh2 : ¬(lt arr2[right] arr2[left]) := maybeSwap_sorted lt_asymm arr1 left right (by omega) (by omega)
  have hh_ : ¬(lt arr_[right] arr_[mid]) := maybeSwap_sorted lt_asymm arr2 mid right (by omega) (by omega)

  suffices ¬(lt arr_[mid] arr_[left]) from ⟨this, hh_⟩

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
