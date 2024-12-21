/-
Copyright (c) 2024 Mombo Solutions, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Chisomo Makombo Sakala
-/

import Batteries.Data.Vector.Basic
import Battteries.Vector.Lemmas
import Quicksort.Utils.RangeHas
import Quicksort.Utils.PermStabalizing
import Batteries.Data.Array.Lemmas
import Battteries.Vector.Lemmas

open Batteries Vector

variable [Ord α]
abbrev lt (x y : α) : Bool :=
  match compare x y with
  | .lt => true
  | _ => false

variable (lt_asymm : ∀ {x y : α}, lt x y → ¬lt y x) (le_trans : ∀ {x y z : α}, ¬lt y x → ¬lt z y → ¬lt z x)

include lt_asymm in
private theorem lt_irrefl : ∀ (x : α), ¬lt x x :=
  fun _ h => (lt_asymm h) h


def Batteries.Vector.maybeSwap (as : Vector α n) (low high : Fin n) : Vector α n :=
  if lt as[high] as[low] then
    as.swap low high
  else
    as

structure Partition (α: Type u) (n : Nat)  where
  arr' : Vector α n
  j' : Nat
  i' : Nat
  deriving Repr

abbrev Partition.Scheme α :=  [Ord α] → {n : Nat} → Vector α n → (left right : Nat) → left < right → right < n →  { x : Partition α n  // left < x.i' ∧ x.j' < right }


theorem maybeSwap_permStabilizing {as : Vector α n} {i j : Fin n} {left right : Nat} (h_i1 : left ≤ i) (h_i2 : i ≤ right) (h_j1 : left ≤ j) (h_j2 : j ≤ right) : PermStabilizing' left right (as.maybeSwap i j) as := by
  unfold maybeSwap
  split
  · apply swap_permStabilizing' <;> assumption
  · rfl

abbrev Partition.IsPartitioned (i j : Nat) (pivot : α) (x : Partition α n) :=
  RangeHas n (¬lt pivot  x.arr'[·]) i x.i' ∧ RangeHas n (¬lt x.arr'[·]  pivot) (x.j' + 1) (j + 1)




include lt_asymm in
private theorem maybeSwap_sorted (as : Vector α n) (low high : Nat) (hlh : low ≤ high) (hn : high < n) : ¬ (lt (maybeSwap as ⟨low, by omega⟩ ⟨high, by omega⟩)[high] (maybeSwap as ⟨low, by omega⟩ ⟨high, by omega⟩)[low]) := by
  unfold maybeSwap; split
  · next h =>
      simp only [lt_asymm h, as.getElem_swap_right, as.getElem_swap_left]
      trivial
  · assumption


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


/-- `while_i` is equivalent to `while arr[i'] < pivot do i' := i' + 1` -/
def Partition.hoare_classic.loop.while_i (left right : Nat) (hr : right < n) (pivot : α) (arr : Vector α n) (i j : Nat) (hjr : j < right) (harltp : ¬lt arr[right] pivot)
  (ival : Nat) (hii : i ≤ ival) (hxi : ival ≤ right) : { i' : Fin n // i ≤ i' ∧ i' ≤ right } :=
  have hi : ival < n := by omega
  if h' : lt arr[ival] pivot /- ∧ ival ≤ j -/ then
    have _ : ival ≠ right := /- by omega -/
      (h' |> show ¬lt arr[ival] pivot by simpa only [·])
    while_i left right hr pivot arr i j hjr harltp   (ival + 1) (by omega) (by omega)
  else
    ⟨⟨ival, by omega⟩, hii, hxi⟩


def Partition.hoare_classic.loop.while_j (left right : Nat) (hr : right < n) (hl : left < n) (pivot : α) (arr : Vector α n) (i j : Nat)  (hjr : j < right) (hli : left < i) (halgep : ¬lt pivot arr[left])
  (jval : Nat) (hxj : left ≤ jval) (hjj : jval ≤ j) : { j' : Fin n // j' ≤ j } :=
  have hj : jval < n := by omega
  if h' : lt pivot arr[jval] /- ∧ i ≤ jval -/ then
    have _ : jval ≠ left := /- by omega -/
      (h' |> show ¬lt pivot arr[jval] by simpa only [·])

    while_j left right hr hl pivot arr i j hjr hli halgep   (jval - 1) (by omega) (by omega)
  else
    ⟨⟨jval, by omega⟩, hjj⟩



def Partition.hoare_classic (arr : Vector α n) (left : Nat)  (right : Nat) (hlr : left < right) (hr : right < n) : {x : Partition α n // (left < x.i') ∧ (x.j' < right)} :=
  have hl : left < n := by omega

  let rec loop (pivot : α) (arr : Vector α n) (i j : Nat) (hli : left < i) (hij : i ≤ j + 1) (hjr : j < right) (halgep : ¬lt pivot arr[left]) (harltp : ¬lt arr[right] pivot) :=

    let ⟨i', _, _⟩ := hoare_classic.loop.while_i left right hr pivot arr i j (by omega) harltp
      i Nat.le.refl (by omega)

    let ⟨j', _⟩  := hoare_classic.loop.while_j left right hr hl pivot arr i' j hjr (by omega) halgep
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

  let mid := left + ((right - left)/2)
  have hm : mid < n := by omega
  let arr_ := arr |> (maybeSwap · ⟨left, hl⟩ ⟨mid, hm⟩) |> (maybeSwap · ⟨left, hl⟩ ⟨right, hr⟩) |> (maybeSwap · ⟨mid, hm⟩ ⟨right, hr⟩)

  let pivot := arr_[mid]

  have : ¬lt pivot arr_[left] ∧ ¬lt arr_[right] pivot :=  median_of_three_sorted sorry /- lt_asymm -/ sorry /- le_trans -/ (by omega) (by omega) hr
  loop pivot arr_ (left + 1) (right - 1) Nat.le.refl (by omega) (by omega) this.left this.right

instance Partition.instInhabitedSchemeOfOrd [Ord α] : Inhabited (Partition.Scheme α) := ⟨Partition.hoare_classic⟩


theorem Partition.hoare_classic.while_i_elem_not_left_of_piv {arr : Vector α n} {harltp : ¬lt arr[right] pivot}
  : ¬lt arr[(hoare_classic.loop.while_i left right hr pivot arr i j hjr harltp ival hii hxi).1.val] pivot := by
  induction ival, hii, hxi using hoare_classic.loop.while_i.induct left right hr pivot arr i j hjr harltp with
  | case1 ival hii hxi hi hlt hir ih =>
    unfold hoare_classic.loop.while_i; simp [*]
  | case2 ival hii hxi hi hle =>
    unfold hoare_classic.loop.while_i; simp [*]


theorem Partition.hoare_classic.while_j_elem_not_right_of_piv {arr : Vector α n} {halgep : ¬lt pivot arr[left]} :
  ¬lt pivot arr[(hoare_classic.loop.while_j left right hr hl pivot arr i j hjr hli halgep   jval hxj hjj).1.val] := by
  induction jval, hxj, hjj using hoare_classic.loop.while_j.induct left right hr hl pivot arr i j hjr hli halgep with
  | case1 jval hxj hjj hj hlt hjl ih =>
    unfold hoare_classic.loop.while_j; simp [*]
  | case2 jval hxj hjj hj  hle =>
    unfold hoare_classic.loop.while_j; simp [*]

theorem Partition.hoare_classic.while_i_before_is_left {arr : Vector α n} {harltp : ¬lt arr[right] pivot} :
  RangeHas n (lt arr[·] pivot) ival (hoare_classic.loop.while_i left right hr pivot arr i j hjr harltp ival hii hxi) := by
  induction ival, hii, hxi using hoare_classic.loop.while_i.induct left right hr pivot arr i j hjr harltp with
  | case1 ival hii hxi hi hlt hir ih =>
    unfold hoare_classic.loop.while_i; simp [*]
    apply RangeHas.prepend <;> assumption
  | case2 ival hii hxi hi hle =>
    unfold hoare_classic.loop.while_i; simp [*]
    apply RangeHas.refl

theorem Partition.hoare_classic.while_j_before_is_right {arr : Vector α n} {halgep : ¬lt pivot arr[left]} :
  RangeHas n (lt pivot arr[·]) ((hoare_classic.loop.while_j left right hr hl pivot arr i j hjr hli halgep   jval hxj hjj) + 1) (jval + 1) := by
  induction jval, hxj, hjj using hoare_classic.loop.while_j.induct left right hr hl pivot arr i j hjr hli halgep with
  | case1 jval hxj hjj hj hlt hjl ih =>
    unfold hoare_classic.loop.while_j; simp [*]
    replace ih := show (jval - 1 + 1) = jval by omega ▸ ih
    apply RangeHas.append <;> assumption
  | case2 jval hxj hjj hj  hle =>
    unfold hoare_classic.loop.while_j; simp [*]
    apply RangeHas.refl

theorem Partition.hoare_classic.loop.partition_bounds {left right : Nat} {hr : right < n} {hl : left < n} {pivot : α} {arr : Vector α n} {i j : Nat} {hli : left < i} {hij : i ≤ j + 1} {hjr : j < right} {halgep : ¬lt pivot arr[left]} {harltp : ¬lt arr[right] pivot} : (loop left right hr hl pivot arr i j hli hij hjr halgep harltp).val.j' < (loop left right hr hl pivot arr i j hli hij hjr halgep harltp).val.i' := by
  induction arr, i, j, hli, hij, hjr, halgep, harltp using loop.induct left right hr hl pivot
  all_goals unfold loop; simp [*]
  · simpa [←Fin.lt_def]
  · omega

protected theorem Partition.hoare_classic.partition_bounds {arr : Vector α n} {left : Nat} {right : Nat} {hlr : left < right} {hr : right < n} : (Partition.hoare_classic arr left right hlr hr).val.j' < (Partition.hoare_classic arr left right hlr hr).val.i' := by
  unfold Partition.hoare_classic
  apply Partition.hoare_classic.loop.partition_bounds

theorem Partition.hoare_classic.loop.permStabilizing {left right : Nat} {hr : right < n} {hl : left < n} {pivot : α} {arr : Vector α n} {i j : Nat} {hli : left < i} {hij : i ≤ j + 1} {hjr : j < right} {halgep : ¬lt pivot arr[left]} {harltp : ¬lt arr[right] pivot} : PermStabilizing' i j (loop left right hr hl pivot arr i j hli hij hjr halgep harltp).val.arr' arr := by
  induction arr, i, j, hli, hij, hjr, halgep, harltp using loop.induct left right hr hl pivot; all_goals unfold loop; simp [*]
  · case case1 arr i j hli hij hjr halgep harltp i' hi1' hi2' heq_i' j' hj' heq_j' hlt arr' halgep' harltp' ih =>
    apply PermStabilizing'.trans
    · apply PermStabilizing'.mono ih <;> omega
    · apply swap_permStabilizing'; all_goals omega
  · case case2 arr i j hli hij hjr halgep harltp i' hi1' hi2' heq_i' j' hj' heq_j' _ hlt' =>
    apply PermStabilizing'.refl
  · case case3 arr i j hli hij hjr halgep harltp i' hi1' hi2' heq_i' j' hj' heq_j' _hij' _hij' =>
    apply PermStabilizing'.refl

protected theorem Partition.hoare_classic.permStabilizing {arr : Vector α n} {left : Nat} {right : Nat} {hlr : left < right} {hr : right < n} : PermStabilizing' left right (Partition.hoare_classic arr left right hlr hr).val.arr' arr := by
  apply PermStabilizing'.trans
  · apply PermStabilizing'.mono hoare_classic.loop.permStabilizing <;> simp_arith
  · apply PermStabilizing'.trans
    apply PermStabilizing'.trans
    all_goals apply maybeSwap_permStabilizing
    all_goals simp only; omega

include lt_asymm in
theorem Partition.hoare_classic.loop.sorted {left right : Nat} {hr : right < n} {hl : left < n} {pivot : α} {arr : Vector α n} {i j : Nat} {hli : left < i} {hij : i ≤ j + 1} {hjr : j < right} {halgep : ¬lt pivot arr[left]} {harltp : ¬lt arr[right] pivot} : IsPartitioned i j pivot (loop left right hr hl pivot arr i j hli hij hjr halgep harltp).val := by
  induction arr, i, j, hli, hij, hjr, halgep, harltp using loop.induct left right hr hl pivot; all_goals unfold loop; simp [*]
  · case case1 arr i j hli hij hjr halgep harltp i' hi1' hi2' heq_i' j' hj' heq_j' hlt arr' halgep' harltp' ih =>
    constructor
    · refine RangeHas.trans ?_ ih.1
      intro k h1 h2
      rw [loop.permStabilizing.2.1 k h2]; exact
      if h : k = i' then by
        simp only [h, Fin.getElem_fin, arr.getElem_swap_left, show j' = _ from Subtype.ext_iff.1 heq_j'.symm]
        exact hoare_classic.while_j_elem_not_right_of_piv
      else by
        have := show (arr.swap ⟨i', _⟩ ⟨j', _⟩)[k] = _ by
          apply arr.getElem_swap_of_ne; all_goals first | simp only ; omega | omega
        simp only [this]
        apply lt_asymm
        replace h2 : k < i' := by omega
        apply hoare_classic.while_i_before_is_left k h1 ((show i' = _ from Subtype.ext_iff.1 heq_i'.symm) ▸ h2)
    · refine RangeHas.trans ih.2 ?_
      intro k h1 h2
      rw [loop.permStabilizing.2.2 k h1]; exact
      if h : k = j' then by
        simp only [h, Fin.getElem_fin, arr.getElem_swap_right, show i' = _ from Subtype.ext_iff.1 heq_i'.symm]
        exact hoare_classic.while_i_elem_not_left_of_piv
      else by
        have := show (arr.swap ⟨i', _⟩ ⟨j', _⟩)[k] = _ by
          apply arr.getElem_swap_of_ne; all_goals first | simp only ; omega | omega
        simp only [this]
        apply lt_asymm
        replace h1 : j' < k := by omega
        apply hoare_classic.while_j_before_is_right k ((show j' = _ from Subtype.ext_iff.1 heq_j'.symm) ▸ h1) h2

  · case case2 arr i j hli hij hjr halgep harltp i' hi1' hi2' heq_i' j' hj' heq_j' _ hlt' =>
    constructor
    · intro k h1 h2
      apply lt_asymm
      have := show i' = _ from Subtype.ext_iff.1 heq_i'.symm
      apply hoare_classic.while_i_before_is_left k h1 (this ▸ h2)
    · intro k h1 h2
      apply lt_asymm
      have := show j' = _ from Subtype.ext_iff.1 heq_j'.symm
      apply hoare_classic.while_j_before_is_right k (this ▸ h1) h2

  · case case3 arr i j hli hij hjr halgep harltp p_ hi1' hi2' heq_i' p hj' heq_j' _hij' _hij' =>
    unfold IsPartitioned at *
    have hij : p = p_ := by omega
    subst hij
    rw [show p.val - 1 + 1 = p by omega]
    constructor
    · apply RangeHas.append
      · change ¬lt pivot arr[p]
        rw [show p = _ from Subtype.ext_iff.1 heq_j'.symm]
        apply hoare_classic.while_j_elem_not_right_of_piv
      · intro k h1 h2
        apply lt_asymm
        have := show p = _ from Subtype.ext_iff.1 heq_i'.symm
        apply while_i_before_is_left k h1 (this ▸ h2)
    · apply RangeHas.prepend
      · change ¬lt arr[p] pivot
        rw [show p = _ from Subtype.ext_iff.1 heq_i'.symm]
        apply hoare_classic.while_i_elem_not_left_of_piv
      · intro k h1 h2
        apply lt_asymm
        have := show p = _ from Subtype.ext_iff.1 heq_j'.symm
        apply hoare_classic.while_j_before_is_right k (this ▸ h1) h2


include le_trans in
include lt_asymm in
protected theorem Partition.hoare_classic.sorted {arr : Vector α n} {left : Nat} {right : Nat} {hlr : left < right} {hr : right < n} : ∃ (pivot : α), IsPartitioned left right pivot (Partition.hoare_classic arr left right hlr hr).val :=
  let mid := left + ((right - left)/2)
  have hlm : left ≤ mid := Nat.le_add_right left ((right - left) / 2)
  have hlr_ :  left ≤ right := Nat.le_of_succ_le hlr
  have hmr :  mid ≤ right :=
    have : ((right - left)/2) ≤ right-left := Nat.div_le_self (right - left) 2
    have : left + ((right - left)/2) ≤ left + (right - left) := Nat.add_le_add_left this left
    Trans.trans this (Nat.add_sub_of_le hlr_)
  have hm :  mid < n := Trans.trans hmr hr

  let arr_ := arr
    |> (maybeSwap · ⟨left, by omega⟩ ⟨mid, by omega⟩)
    |> (maybeSwap · ⟨left, by omega⟩ ⟨right, by omega⟩)
    |> (maybeSwap · ⟨mid, by omega⟩ ⟨right, by omega⟩)
  let pivot := arr_[mid]

  have hh2 : ¬lt pivot arr_[left] ∧ ¬lt arr_[right] pivot := median_of_three_sorted (lt_asymm := lt_asymm) (le_trans := le_trans) hlm hmr hr
  let x : Partition α n := (hoare_classic.loop left right hr (by omega) pivot  arr_ (left + 1) (right - 1) (by omega) (by omega) (by omega) hh2.left hh2.right).val

  have : IsPartitioned left right pivot x := by
    have hh1 : IsPartitioned (left + 1) (right - 1) pivot x := hoare_classic.loop.sorted (lt_asymm := lt_asymm)

    have : PermStabilizing' (left + 1) (right - 1) x.arr' arr_ := hoare_classic.loop.permStabilizing
    replace hh2 : ¬lt pivot x.arr'[left] ∧ ¬lt x.arr'[right] pivot := by
      have heq_left : x.arr'[left] = arr_[left] := this.2.1 ⟨left, by omega⟩ (by simp_arith)
      have heq_right : x.arr'[right] = arr_[right] := this.2.2 ⟨right, by omega⟩ (by simp_arith; omega)
      rwa [heq_left, heq_right]

    have hh1_right : RangeHas n (¬lt x.arr'[·]  pivot) (x.j' + 1) right := by
      have : right - 1 + 1 = right := by omega
      rw [←this]; exact hh1.right
    exact ⟨RangeHas.prepend (ha := by omega) hh2.left hh1.left , RangeHas.append (hb := by omega) hh2.right hh1_right⟩
  ⟨pivot, this⟩

class Partition.LawfulScheme (part : Partition.Scheme α) : Prop where
  partitionBounds : (part as left right hlr hr).val.j' < (part as left right hlr hr).val.i'
  permStabilizing : PermStabilizing' left right (part as left right hlr hr).val.arr' as
  sorting (lt_asymm : ∀ {x y : α}, lt x y → ¬lt y x) (le_trans : ∀ {x y z : α}, ¬lt y x → ¬lt z y → ¬lt z x) (as : Vector α n) (hlr : left < right) (hr : right < n) : ∃ (pivot : α), IsPartitioned left right pivot (part as left right hlr hr).val

instance Partition.instLawfulHoareClassicScheme : LawfulScheme (α := α) hoare_classic where
  partitionBounds := hoare_classic.partition_bounds
  permStabilizing := hoare_classic.permStabilizing
  sorting lt_asymm le_trans _ _ _ := hoare_classic.sorted lt_asymm le_trans


instance  Partition.instLawfulDefaultScheme   : LawfulScheme (α := α) (@default _ _) := by
  simp only [default]; apply Partition.instLawfulHoareClassicScheme

@[inline]
def qs [Ord α] (arr : Array α) (left : Nat := 0) (right : Nat := arr.size - 1) (part : Partition.Scheme α := @default _ _) : Array α :=
  let rec @[specialize]
  strict {n : Nat} (as : Batteries.Vector α n) (left : Nat := 0) (right : Nat := n - 1) (hsize' : right ≤ n - 1) : Batteries.Vector α n :=
    if hlr : left < right then
      let ⟨⟨as', j', i'⟩, (_ : _ < i'), (_ : j' < _ )⟩ := part as left right hlr (by omega)
      let as := qs.strict as' left j' (by omega)
      let as := qs.strict as i' right (by omega)
      as
    else
      as
    termination_by right - left

  let right' : Nat := if right ≤ arr.size - 1 then right else
    have := Inhabited.mk (arr.size - 1)
    panic! "index out of bounds"

  have : right' ≤ arr.size - 1 := by
    simp [right']; split <;> simp [panicWithPosWithDecl, panic, panicCore, *]

  qs.strict ⟨arr, rfl⟩ left right' this |>.1

open Partition


theorem qs.strict.permStabilizing [LawfulScheme part] {as : Vector α n} {left right : Nat} {hsize' : right ≤ n - 1} : PermStabilizing' left right (qs.strict part as left right hsize') as := by
  induction as, left, right, hsize' using qs.strict.induct (part := part) with
  | case1 as left right hsize' hlr as' j' i' hli hjr heq as'' ih1 _ih1 ih2 =>
    unfold qs.strict; simp [*]
    have ih0 := heq ▸ LawfulScheme.permStabilizing (part := part)
    replace ih1 : PermStabilizing' left right .. := ih1.mono (by omega) (by omega)
    replace ih2 : PermStabilizing' left right .. := ih2.mono (by omega) (by omega)
    exact ih2 |>.trans ih1 |>.trans ih0
  | case2 as left right hsize' hlr =>
    unfold qs.strict; simp [*]
    apply PermStabilizing'.refl

theorem qs.perm' [LawfulScheme part] {as : Array α} {left : Nat} {right : Nat}  : qs as left right part ~ as := by
  simp only [qs]; split
  any_goals simp only [panicWithPosWithDecl, panic, panicCore, *]
  all_goals exact qs.strict.permStabilizing.1

theorem qs.perm {as : Array α} : qs as ~ as := qs.perm'

@[simp]
theorem qs.qs_size [LawfulScheme part] {as : Array α} :
    (qs as left right part).size = as.size := qs.perm'.length_eq

include le_trans in
include lt_asymm in
theorem qs.strict.monotonic [LawfulScheme part] {as : Vector α n} {hsize' : right ≤ n - 1} : let q := (qs.strict part as left right hsize'); ∀ (i j : Fin n), (left ≤ i) → (i < j) → (j ≤ right) → ¬lt q[j] q[i] := by
  induction as, left, right, hsize' using qs.strict.induct (part := part) with
  | case1 as left right hsize' hlr as' j' i' hli' hjr' heq as'' ih1 _ih1 ih2 =>
    unfold qs.strict; simp only [↓reduceDIte, hlr, heq]

    intro i j hli hij hjr; exact

    have hji' : j' < i' := by apply heq
      ▸ LawfulScheme.partitionBounds (part := part)
    let as''' := qs.strict part as'' i' right (by omega)

    if hhi : i' ≤ i then by
      apply ih2 <;> assumption
    else if hhj : j ≤ j' then by
      rw [qs.strict.permStabilizing.2.left j (by omega), qs.strict.permStabilizing.2.left i (by omega)]
      apply ih1 <;> assumption
    else by
      replace hhi : i < i' := by omega
      replace hhj : j' < j := by omega

      have ⟨pivot, ih0⟩ := LawfulScheme.sorting (part := part) lt_asymm le_trans as hlr (by omega)
      -- ih0 : Partitioned left right pivot (part as left right hlr hr).val

      replace ih0 :
          (∀ (i : Fin n), left ≤ i → i < i' → ¬lt pivot as'[i]) ∧
          (∀ (j : Fin n), j' + 1 ≤ j → j < right + 1 → ¬lt as'[j] pivot) := by
        unfold Partition.IsPartitioned at ih0; rwa [heq] at ih0

      have hhh1 : ¬lt pivot as'''[i] :=
        suffices ¬lt pivot as''[i] by rwa [qs.strict.permStabilizing.2.left i (by omega)]
        if _ : i ≤ j' then by
          apply PermStabilizing'.invariance (motive := (¬lt pivot ·)) (left := left) (hi := j' + 1) (h := ?_ )
          any_goals omega
          · exact qs.strict.permStabilizing
          · intro i_ _ _
            apply ih0.left i_ <;> omega
        else by
          rw [qs.strict.permStabilizing.2.right _ ?_]
          apply ih0.left i
          all_goals omega

      have hhh2 : ¬lt as'''[j] pivot :=
        if _ : i' ≤ j then by
          apply PermStabilizing'.invariance (motive := (¬lt · pivot)) (left := i') (hi := right + 1) (h := ?_)
          any_goals omega
          · exact qs.strict.permStabilizing
          · intro j_ _ _
            rw [qs.strict.permStabilizing.2.right j_ (by omega)]
            apply ih0.right j_ <;> omega
        else by
          rw [qs.strict.permStabilizing.2.left _ ?_, qs.strict.permStabilizing.2.right _ ?_]
          apply ih0.right j
          all_goals omega
      exact le_trans hhh1 hhh2
  | case2 => omega

include le_trans in
include lt_asymm in
theorem qs.monotonic' {as : Array α} {left : Nat} {right : Nat} {part : Partition.Scheme α} [LawfulScheme part] :  let q := (qs as left right part); ∀ (i j : Fin q.size), (left ≤ i) → (i < j) → (j ≤ right) → ¬lt q[j] q[i] := by
  simp only
  intro  i j _ _ _
  have _ : j.cast qs.qs_size ≤ as.size - 1 := by omega
  simp only [qs]; split
  any_goals simp only [panicWithPosWithDecl, panic, panicCore, *]
  all_goals apply qs.strict.monotonic lt_asymm le_trans (i.cast qs.qs_size) (j.cast qs.qs_size) <;> assumption

include le_trans in
include lt_asymm in
theorem qs.monotonic {as : Array α} {part : Partition.Scheme α} [LawfulScheme part]: ∀ (i j : Fin (qs (part := part) as).size), i < j → ¬lt (qs (part := part) as)[j] (qs (part := part) as)[i] := by
  intro i j h
  apply qs.monotonic' lt_asymm le_trans
  · omega
  · exact h
  · have := j.2; simp only [qs.qs_size] at this; omega

include le_trans in
include lt_asymm in
theorem qs.monotonic_with_defaults  {as : Array α} : ∀ (i j : Fin (qs as).size), i < j → ¬lt (qs as)[j] (qs as)[i] := qs.monotonic lt_asymm le_trans

include le_trans in
include lt_asymm in
example {as : Array α} : let q := (qs (part := Partition.hoare_classic) as); ∀ (i j : Fin q.size), i < j → ¬lt q[j] q[i] := qs.monotonic lt_asymm le_trans
