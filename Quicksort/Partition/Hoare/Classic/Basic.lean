import Quicksort.Partition.Init.Basic
import Battteries.Vector.Lemmas

open Batteries Vector

namespace Partition

variable [Ord α]
variable (lt_asymm : ∀ {x y : α}, lt x y → ¬lt y x)

include lt_asymm in
private theorem lt_irrefl : ∀ (x : α), ¬lt x x :=
  fun _ h => (lt_asymm h) h

include lt_asymm in
private theorem maybeSwap_sorted (as : Vector α n) (low high : Nat) (hlh : low ≤ high) (hn : high < n) : ¬ (lt (maybeSwap as ⟨low, by omega⟩ ⟨high, by omega⟩)[high] (maybeSwap as ⟨low, by omega⟩ ⟨high, by omega⟩)[low]) := by
  unfold maybeSwap; split
  · next h =>
      simp only [lt_asymm h, as.getElem_swap_right, as.getElem_swap_left]
      trivial
  · assumption

variable (le_trans : ∀ {x y z : α}, ¬lt y x → ¬lt z y → ¬lt z x)
-- set_option trace.profiler true in
include lt_asymm in
include le_trans in
private theorem median_of_three_sorted {arr : Vector α n} {left mid right: Nat} (hlm : left ≤ mid) (hmr : mid ≤ right) (hr : right < n) :
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
    · have : (arr2.swap ⟨mid, ‹_›⟩ ⟨right, ‹_›⟩)[left] = _ :=
        arr2.getElem_swap_of_ne _ hleqm hlneqr
      simp only [this, arr2.getElem_swap_left, Fin.getElem_fin]
      assumption
    · exact
      if hmeqr : mid = right then by
        simp only [hmeqr]
        exact hh2
      else by
        simp only [arr2]
        unfold maybeSwap
        split

        · have : (arr1.swap ⟨left, by omega⟩ ⟨right, hr⟩)[mid] = _ :=
            arr1.getElem_swap_of_ne (_ : mid < n) (Ne.symm hleqm) hmeqr
          simp only [this, arr1.getElem_swap_left, Fin.getElem_fin]
          refine le_trans (lt_asymm ?_) hh1
          assumption
        · assumption

-- set_option trace.profiler true in
/-- `while_i` is equivalent to `while arr[i'] < pivot do i' := i' + 1` -/
def hoare.classic.loop.while_i (left right : Nat) (hr : right < n) (pivot : α) (arr : Vector α n) (i j : Nat) (hjr : j < right) (harltp : ¬lt arr[right] pivot)
  (ival : Nat) (hii : i ≤ ival) (hxi : ival ≤ right) : { i' : Fin n // i ≤ i' ∧ i' ≤ right } :=
  have hi : ival < n := by omega
  if h' : lt arr[ival] pivot /- ∧ ival ≤ j -/ then
    have _ : ival ≠ right := /- by omega -/
      (h' |> show ¬lt arr[ival] pivot by simpa only [·])
    hoare.classic.loop.while_i left right hr pivot arr i j hjr harltp   (ival + 1) (by omega) (by omega)
  else
    ⟨⟨ival, by omega⟩, hii, hxi⟩


def hoare.classic.loop.while_j (left right : Nat) (hr : right < n) (hl : left < n) (pivot : α) (arr : Vector α n) (i j : Nat)  (hjr : j < right) (hli : left < i) (halgep : ¬lt pivot arr[left])
  (jval : Nat) (hxj : left ≤ jval) (hjj : jval ≤ j) : { j' : Fin n // j' ≤ j } :=
  have hj : jval < n := by omega
  if h' : lt pivot arr[jval] /- ∧ i ≤ jval -/ then
    have _ : jval ≠ left := /- by omega -/
      (h' |> show ¬lt pivot arr[jval] by simpa only [·])

    hoare.classic.loop.while_j left right hr hl pivot arr i j hjr hli halgep   (jval - 1) (by omega) (by omega)
  else
    ⟨⟨jval, by omega⟩, hjj⟩



include lt_asymm in
include le_trans in
def hoare.classic (arr : Vector α n) (left : Nat)  (right : Nat) (hlr : left < right) (hr : right < n) : {x : Partition α n // (left < x.i') ∧ (x.j' < right)} :=
  have hl : left < n := by omega

  let rec loop (pivot : α) (arr : Vector α n) (i j : Nat) (hli : left < i) (hij : i ≤ j + 1) (hjr : j < right) (halgep : ¬lt pivot arr[left]) (harltp : ¬lt arr[right] pivot) :=

    let ⟨i', _, _⟩ := hoare.classic.loop.while_i left right hr pivot arr i j (by omega) harltp
      i Nat.le.refl (by omega)

    let ⟨j', _⟩  := hoare.classic.loop.while_j left right hr hl pivot arr i' j hjr (by omega) halgep
      j (by omega) Nat.le.refl

    if _ : i' < j' then
      let arr' := arr.swap i' j'
      have halgep' : ¬lt pivot arr'[left]  := by simp only [show arr'[left] = _ by apply Vector.getElem_swap_of_ne ..; all_goals omega]; exact halgep
      have harltp' : ¬lt arr'[right] pivot := by simp only [show arr'[right] = _ by apply Vector.getElem_swap_of_ne ..; all_goals omega]; exact harltp

      loop pivot arr' (i' + 1) (j' - 1) (by omega) (by omega) (by omega) halgep' harltp'
    else if _ : j' < i' then
      ⟨⟨arr, j', i'⟩, by simp; omega, by simp; omega⟩
    else -- have _ : j' = i' := by omega
      ⟨⟨arr, j' - 1, i' + 1⟩, by simp; omega, by simp; omega⟩
  -- termination_by j + 1 - i
  -- decreasing_by omega

  let mid := left + ((right - left)/2)
  have hm : mid < n := by omega
  let arr_ := arr |> (maybeSwap · ⟨left, hl⟩ ⟨mid, hm⟩) |> (maybeSwap · ⟨left, hl⟩ ⟨right, hr⟩) |> (maybeSwap · ⟨mid, hm⟩ ⟨right, hr⟩)

  let pivot := arr_[mid]

  have : ¬lt pivot arr_[left] ∧ ¬lt arr_[right] pivot :=  median_of_three_sorted lt_asymm /- lt_asymm -/ le_trans /- le_trans -/ (by omega) (by omega) hr
  loop pivot arr_ (left + 1) (right - 1) Nat.le.refl (by omega) (by omega) this.left this.right
