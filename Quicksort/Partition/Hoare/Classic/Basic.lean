import Quicksort.Partition.Init.Basic
import Quicksort.Partition.Init.MedianOfThree


open Vector

namespace Partition

variable [Ord α]
variable (lt_asymm : ∀ {x y : α}, lt x y → ¬lt y x)
variable (le_trans : ∀ {x y z : α}, ¬lt y x → ¬lt z y → ¬lt z x)


-- set_option trace.profiler true in
/-- `while_i` is equivalent to `while arr[i'] < pivot do i' := i' + 1` -/
@[inline]
def hoare.classic.loop.while_i (left right : Nat) (hr : right < n) (pivot : α) (arr : Vector α n)
    (i j : Nat) (hjr : j < right) (harltp : ¬lt arr[right] pivot)
    (ival : Nat) (hii : i ≤ ival) (hxi : ival ≤ right) : { i' : Fin n // i ≤ i' ∧ i' ≤ right } :=
  have hi : ival < n := by omega
  if h' : lt arr[ival] pivot /- ∧ ival ≤ j -/ then
    have _ : ival ≠ right := /- by omega -/
      (h' |> show ¬lt arr[ival] pivot by simpa only [·])
    while_i left right hr pivot arr i j hjr harltp   (ival + 1) (by omega) (by omega)
  else
    ⟨⟨ival, by omega⟩, hii, hxi⟩

@[inline]
def hoare.classic.loop.while_j (left right : Nat) (hr : right < n) (hl : left < n) (pivot : α)
    (arr : Vector α n) (i j : Nat)  (hjr : j < right) (hli : left < i) (halgep : ¬lt pivot arr[left])
    (jval : Nat) (hxj : left ≤ jval) (hjj : jval ≤ j) : { j' : Fin n // j' ≤ j } :=
  have hj : jval < n := by omega
  if h' : lt pivot arr[jval] /- ∧ i ≤ jval -/ then
    have _ : jval ≠ left := /- by omega -/
      (h' |> show ¬lt pivot arr[jval] by simpa only [·])
    while_j left right hr hl pivot arr i j hjr hli halgep   (jval - 1) (by omega) (by omega)
  else
    ⟨⟨jval, by omega⟩, hjj⟩



include lt_asymm in
include le_trans in
@[inline]
def hoare.classic (arr : Vector α n) (left : Nat)  (right : Nat) (hlr : left < right)
    (hr : right < n) : {x : Partition α n // (left < x.i') ∧ (x.j' < right)} :=
  have hl : left < n := by omega

  let rec @[specialize] loop (pivot : α) (arr : Vector α n) (i j : Nat) (hli : left < i)
      (hij : i ≤ j + 1) (hjr : j < right) (halgep : ¬lt pivot arr[left]) (harltp : ¬lt arr[right] pivot) :=

    let ⟨i', _, _⟩ := hoare.classic.loop.while_i left right hr pivot arr i j (by omega) harltp
      i Nat.le.refl (by omega)

    let ⟨j', _⟩  := hoare.classic.loop.while_j left right hr hl pivot arr i' j hjr (by omega) halgep
      j (by omega) Nat.le.refl

    if _ : i' < j' then
      let arr' := arr.swap i' j'
      have halgep' : ¬lt pivot arr'[left]  := by
        simp only [show arr'[left] = _ by apply Vector.getElem_swap_of_ne ..; all_goals omega]
        exact halgep
      have harltp' : ¬lt arr'[right] pivot := by
        simp only [show arr'[right] = _ by apply Vector.getElem_swap_of_ne ..; all_goals omega]
        exact harltp

      loop pivot arr' (i' + 1) (j' - 1) (by omega) (by omega) (by omega) halgep' harltp'
    else if _ : j' < i' then
      ⟨⟨arr, j', i'⟩, by simp; omega, by simp; omega⟩
    else -- have _ : j' = i' := by omega
      ⟨⟨arr, j' - 1, i' + 1⟩, by simp; omega, by simp; omega⟩
  -- termination_by j + 1 - i
  -- decreasing_by omega

  let mid := left + ((right - left)/2)
  have hm : mid < n := by omega
  let arr_ := arr
    |> (maybeSwap · ⟨left, hl⟩ ⟨mid, hm⟩)
    |> (maybeSwap · ⟨left, hl⟩ ⟨right, hr⟩)
    |> (maybeSwap · ⟨mid, hm⟩ ⟨right, hr⟩)

  let pivot := arr_[mid]

  have : ¬lt pivot arr_[left] ∧ ¬lt arr_[right] pivot :=
    median_of_three_sorted lt_asymm le_trans (by omega) (by omega) hr
  loop pivot arr_ (left + 1) (right - 1) Nat.le.refl (by omega) (by omega) this.left this.right
