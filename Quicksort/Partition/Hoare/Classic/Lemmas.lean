
import Quicksort.Partition.Hoare.Classic.Basic
import Quicksort.Partition.Init.Lemmas

open Batteries Vector

namespace Partition
variable [Ord α]
variable (lt_asymm : ∀ {x y : α}, lt x y → ¬lt y x)

include lt_asymm in
private theorem lt_irrefl : ∀ (x : α), ¬lt x x :=
  fun _ h => (lt_asymm h) h


variable (le_trans : ∀ {x y z : α}, ¬lt y x → ¬lt z y → ¬lt z x)


theorem hoare.classic.while_i_elem_not_left_of_piv {arr : Vector α n} {harltp : ¬lt arr[right] pivot}
  : ¬lt arr[(hoare.classic.loop.while_i left right hr pivot arr i j hjr harltp ival hii hxi).1.val] pivot := by
  induction ival, hii, hxi using hoare.classic.loop.while_i.induct left right hr pivot arr i j hjr harltp with
  | case1 ival hii hxi hi hlt hir ih =>
    unfold hoare.classic.loop.while_i; simp [*]
  | case2 ival hii hxi hi hle =>
    unfold hoare.classic.loop.while_i; simp [*]


theorem hoare.classic.while_j_elem_not_right_of_piv {arr : Vector α n} {halgep : ¬lt pivot arr[left]} :
  ¬lt pivot arr[(hoare.classic.loop.while_j left right hr hl pivot arr i j hjr hli halgep   jval hxj hjj).1.val] := by
  induction jval, hxj, hjj using hoare.classic.loop.while_j.induct left right hr hl pivot arr i j hjr hli halgep with
  | case1 jval hxj hjj hj hlt hjl ih =>
    unfold hoare.classic.loop.while_j; simp [*]
  | case2 jval hxj hjj hj  hle =>
    unfold hoare.classic.loop.while_j; simp [*]




theorem hoare.classic.while_i_before_is_left {arr : Vector α n} {harltp : ¬lt arr[right] pivot} :
  RangeHas n (lt arr[·] pivot) ival (hoare.classic.loop.while_i left right hr pivot arr i j hjr harltp ival hii hxi) := by
  induction ival, hii, hxi using hoare.classic.loop.while_i.induct left right hr pivot arr i j hjr harltp with
  | case1 ival hii hxi hi hlt hir ih =>
    unfold hoare.classic.loop.while_i; simp [*]
    apply RangeHas.prepend <;> assumption
  | case2 ival hii hxi hi hle =>
    unfold hoare.classic.loop.while_i; simp [*]
    apply RangeHas.refl


theorem hoare.classic.while_j_before_is_right {arr : Vector α n} {halgep : ¬lt pivot arr[left]} :
  RangeHas n (lt pivot arr[·]) ((hoare.classic.loop.while_j left right hr hl pivot arr i j hjr hli halgep   jval hxj hjj) + 1) (jval + 1) := by
  induction jval, hxj, hjj using hoare.classic.loop.while_j.induct left right hr hl pivot arr i j hjr hli halgep with
  | case1 jval hxj hjj hj hlt hjl ih =>
    unfold hoare.classic.loop.while_j; simp [*]
    replace ih := show (jval - 1 + 1) = jval by omega ▸ ih
    apply RangeHas.append <;> assumption
  | case2 jval hxj hjj hj  hle =>
    unfold hoare.classic.loop.while_j; simp [*]
    apply RangeHas.refl


theorem hoare.classic.loop.partition_bounds {left right : Nat} {hr : right < n} {hl : left < n} {pivot : α} {arr : Vector α n} {i j : Nat} {hli : left < i} {hij : i ≤ j + 1} {hjr : j < right} {halgep : ¬lt pivot arr[left]} {harltp : ¬lt arr[right] pivot} : (loop left right hr hl pivot arr i j hli hij hjr halgep harltp).val.j' < (loop left right hr hl pivot arr i j hli hij hjr halgep harltp).val.i' := by
  induction arr, i, j, hli, hij, hjr, halgep, harltp using loop.induct left right hr hl pivot; all_goals unfold loop; simp [*]
  -- · case  case1 arr i j hli hij hjr halgep harltp i' hi1' hi2' heq_i' j' hj' heq_j' hlt arr' halgep' harltp' ih =>
    -- unfold loop; simp [*]
  · case case2 arr i j hli hij hjr halgep harltp i' hi1' hi2' heq_i' j' hj' heq_j' _ hlt' =>
    -- unfold loop; simp [*]
    simpa [←Fin.lt_def]
  · case case3 arr i j hli hij hjr halgep harltp i' hi1' hi2' heq_i' j' hj' heq_j' _hij' _hij' =>
    -- unfold loop; simp [*] -- have hij : i' = j' := by omega
    omega

theorem hoare.classic.loop.permStabilizing {left right : Nat} {hr : right < n} {hl : left < n} {pivot : α} {arr : Vector α n} {i j : Nat} {hli : left < i} {hij : i ≤ j + 1} {hjr : j < right} {halgep : ¬lt pivot arr[left]} {harltp : ¬lt arr[right] pivot} : PermStabilizing' i j (loop left right hr hl pivot arr i j hli hij hjr halgep harltp).val.arr' arr := by
  induction arr, i, j, hli, hij, hjr, halgep, harltp using loop.induct left right hr hl pivot; all_goals unfold loop; simp [*]
  · case case1 arr i j hli hij hjr halgep harltp i' hi1' hi2' heq_i' j' hj' heq_j' hlt arr' halgep' harltp' ih =>
    apply PermStabilizing'.trans
    · apply PermStabilizing'.mono ih <;> omega
    · apply swap_permStabilizing'; all_goals omega
  · case case2 arr i j hli hij hjr halgep harltp i' hi1' hi2' heq_i' j' hj' heq_j' _ hlt' =>
    apply PermStabilizing'.refl
  · case case3 arr i j hli hij hjr halgep harltp i' hi1' hi2' heq_i' j' hj' heq_j' _hij' _hij' =>
    apply PermStabilizing'.refl


-- set_option trace.profiler true in
include lt_asymm in
theorem hoare.classic.loop.sorted {left right : Nat} {hr : right < n} {hl : left < n} {pivot : α} {arr : Vector α n} {i j : Nat} {hli : left < i} {hij : i ≤ j + 1} {hjr : j < right} {halgep : ¬lt pivot arr[left]} {harltp : ¬lt arr[right] pivot} : IsPartitioned i j pivot (loop left right hr hl pivot arr i j hli hij hjr halgep harltp).val := by
  induction arr, i, j, hli, hij, hjr, halgep, harltp using loop.induct left right hr hl pivot; all_goals unfold loop; simp [*]
  · case case1 arr i j hli hij hjr halgep harltp i' hi1' hi2' heq_i' j' hj' heq_j' hlt arr' halgep' harltp' ih =>
    constructor
    · refine RangeHas.trans ?_ ih.1
      intro k h1 h2
      rw [loop.permStabilizing.2.1 k h2]; exact
      if h : k = i' then by
        simp only [h, Fin.getElem_fin, arr.getElem_swap_left, show j' = _ from Subtype.ext_iff.1 heq_j'.symm]
        exact hoare.classic.while_j_elem_not_right_of_piv
      else by
        have := show (arr.swap ⟨i', _⟩ ⟨j', _⟩)[k] = _ by
          apply arr.getElem_swap_of_ne; all_goals first | simp only ; omega | omega
        simp only [this]
        apply lt_asymm
        replace h2 : k < i' := by omega
        apply hoare.classic.while_i_before_is_left k h1 ((show i' = _ from Subtype.ext_iff.1 heq_i'.symm) ▸ h2)
    · refine RangeHas.trans ih.2 ?_
      intro k h1 h2
      rw [loop.permStabilizing.2.2 k h1]; exact
      if h : k = j' then by
        simp only [h, Fin.getElem_fin, arr.getElem_swap_right, show i' = _ from Subtype.ext_iff.1 heq_i'.symm]
        exact hoare.classic.while_i_elem_not_left_of_piv
      else by
        have := show (arr.swap ⟨i', _⟩ ⟨j', _⟩)[k] = _ by
          apply arr.getElem_swap_of_ne; all_goals first | simp only ; omega | omega
        simp only [this]
        apply lt_asymm
        replace h1 : j' < k := by omega
        apply hoare.classic.while_j_before_is_right k ((show j' = _ from Subtype.ext_iff.1 heq_j'.symm) ▸ h1) h2

  · case case2 arr i j hli hij hjr halgep harltp i' hi1' hi2' heq_i' j' hj' heq_j' _ hlt' =>
    -- apply while_before_is_partitioned <;> assumption
    constructor
    · intro k h1 h2
      apply lt_asymm
      have := show i' = _ from Subtype.ext_iff.1 heq_i'.symm
      apply hoare.classic.while_i_before_is_left k h1 (this ▸ h2)
    · intro k h1 h2
      apply lt_asymm
      have := show j' = _ from Subtype.ext_iff.1 heq_j'.symm
      apply hoare.classic.while_j_before_is_right k (this ▸ h1) h2

  · case case3 arr i j hli hij hjr halgep harltp p_ hi1' hi2' heq_i' p hj' heq_j' _hij' _hij' =>

    -- have this : IsPartitioned i j pivot ⟨arr, p, p_⟩ := by apply while_before_is_partitioned <;> assumption

    unfold IsPartitioned at *
    have hij : p = p_ := by omega
    subst hij
    rw [show p.val - 1 + 1 = p by omega]
    constructor
    · apply RangeHas.append
      · change ¬lt pivot arr[p]
        rw [show p = _ from Subtype.ext_iff.1 heq_j'.symm]
        apply hoare.classic.while_j_elem_not_right_of_piv
      ·
        -- exact this.1
        intro k h1 h2
        apply lt_asymm
        have := show p = _ from Subtype.ext_iff.1 heq_i'.symm
        apply while_i_before_is_left k h1 (this ▸ h2)
    · apply RangeHas.prepend
      · change ¬lt arr[p] pivot
        rw [show p = _ from Subtype.ext_iff.1 heq_i'.symm]
        apply hoare.classic.while_i_elem_not_left_of_piv
      ·
        -- exact this.2
        intro k h1 h2
        apply lt_asymm
        have := show p = _ from Subtype.ext_iff.1 heq_j'.symm
        apply hoare.classic.while_j_before_is_right k (this ▸ h1) h2

-- -----------------------



include lt_asymm in
private theorem hoare.classic.sortAt_sorted (as : Vector α n) (low high : Nat) (hlh : low ≤ high) (hn : high < n) : ¬ (lt (maybeSwap as ⟨low, by omega⟩ ⟨high, by omega⟩)[high] (maybeSwap as ⟨low, by omega⟩ ⟨high, by omega⟩)[low]) := by
  unfold maybeSwap; split
  · next h =>
      have _ := lt_asymm h
      simp_all [as.getElem_swap_right, as.getElem_swap_left]
  · assumption

-- set_option trace.profiler true in
include lt_asymm in
include le_trans in
private theorem hoare.classic.median_of_three_sorted {arr : Vector α n} {left mid right: Nat} (hlm : left ≤ mid) (hmr : mid ≤ right) (hr : right < n) :
  let_fun arr_ := arr
    |> (maybeSwap · ⟨left, by omega⟩ ⟨mid, by omega⟩)
    |> (maybeSwap · ⟨left, by omega⟩ ⟨right, by omega⟩)
    |> (maybeSwap · ⟨mid, by omega⟩ ⟨right, by omega⟩)
-- ∀ {k_ : Nat} (_ : left ≤ k_) (_ : k_ ≤ right),
  ¬lt arr_[mid] arr_[left] ∧ ¬lt arr_[right] arr_[mid]
  :=
  have _ : left < n := by omega
  have _ : mid < n := by omega

  let arr1 : Vector α n := maybeSwap arr ⟨left, by omega⟩ ⟨mid, by omega⟩
  let arr2 : Vector α n := maybeSwap arr1 ⟨left, by omega⟩ ⟨right, by omega⟩
  let arr_ : Vector α n := maybeSwap arr2 ⟨mid, by omega⟩ ⟨right, by omega⟩

  have hh1 : ¬lt arr1[mid] arr1[left] := sortAt_sorted lt_asymm arr left mid (by omega) (by omega)
  have hh2 : ¬lt arr2[right] arr2[left] := sortAt_sorted lt_asymm arr1 left right (by omega) (by omega)
  have hh_ : ¬lt arr_[right] arr_[mid] := sortAt_sorted lt_asymm arr2 mid right (by omega) (by omega)

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


include le_trans in
include lt_asymm in
protected theorem hoare.classic.partition_bounds' {arr : Vector α n} {left : Nat} {right : Nat} {hlr : left < right} {hr : right < n} : (hoare.classic (lt_asymm := lt_asymm) (le_trans := le_trans) arr left right hlr hr).val.j' < (hoare.classic (lt_asymm := lt_asymm) (le_trans := le_trans) arr left right hlr hr).val.i' := by
  unfold hoare.classic
  apply Partition.hoare.classic.loop.partition_bounds


include le_trans in
include lt_asymm in
protected theorem hoare.classic.permStabilizing' {arr : Vector α n} {left : Nat} {right : Nat} {hlr : left < right} {hr : right < n} : PermStabilizing' left right (hoare.classic (lt_asymm := lt_asymm) (le_trans := le_trans) arr left right hlr hr).val.arr' arr := by
  apply PermStabilizing'.trans
  · apply PermStabilizing'.mono hoare.classic.loop.permStabilizing <;> simp_arith
  · apply PermStabilizing'.trans
    apply PermStabilizing'.trans
    all_goals apply maybeSwap_permStabilizing
    all_goals simp only; omega


include le_trans in
include lt_asymm in
protected theorem hoare.classic.sorted {arr : Vector α n} {left : Nat} {right : Nat} {hlr : left < right} {hr : right < n} : ∃ (pivot : α), IsPartitioned left right pivot (hoare.classic (lt_asymm := lt_asymm) (le_trans := le_trans) arr left right hlr hr).val :=

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

  have hh2 : ¬lt pivot arr_[left] ∧ ¬lt arr_[right] pivot := hoare.classic.median_of_three_sorted (lt_asymm := lt_asymm) (le_trans := le_trans) hlm hmr hr
  let x : Partition α n := (hoare.classic.loop left right hr (by omega) pivot  arr_ (left + 1) (right - 1) (by omega) (by omega) (by omega) hh2.left hh2.right).val

  have : IsPartitioned left right pivot x := by
    have hh1 : IsPartitioned (left + 1) (right - 1) pivot x := hoare.classic.loop.sorted (lt_asymm := lt_asymm)

    have : PermStabilizing' (left + 1) (right - 1) x.arr' arr_ := hoare.classic.loop.permStabilizing
    replace hh2 : ¬lt pivot x.arr'[left] ∧ ¬lt x.arr'[right] pivot := by
      have heq_left : x.arr'[left] = arr_[left] := this.2.1 ⟨left, by omega⟩ (by simp_arith)
      have heq_right : x.arr'[right] = arr_[right] := this.2.2 ⟨right, by omega⟩ (by simp_arith; omega)
      rwa [heq_left, heq_right]

    have hh1_right : RangeHas n (¬lt x.arr'[·]  pivot) (x.j' + 1) right := by
      have : right - 1 + 1 = right := by omega
      rw [←this]; exact hh1.right
    exact ⟨RangeHas.prepend (ha := by omega) hh2.left hh1.left , RangeHas.append (hb := by omega) hh2.right hh1_right⟩
  ⟨pivot, this⟩
