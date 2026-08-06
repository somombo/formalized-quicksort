import Quicksort.Init.RangeHas
import Quicksort.Init.PermStabalizing

import Upstream.HoareQSort.Basic

open Vector

theorem maybeSwap_permStabilizing [Ord α] {as : Vector α n} {i j : Fin n} {left right : Nat} (h_i1 : left ≤ i) (h_i2 : i ≤ right) (h_j1 : left ≤ j) (h_j2 : j ≤ right) : PermStabilizing' left right (as.maybeSwap i j) as := by
  unfold maybeSwap
  split
  · apply swap_permStabilizing' <;> assumption
  · rfl

-- given j' < i' then ∃ piv, ∀ i_ ∈ [i, i'), arr'[i_] ≤ piv ∧ ∀ j_ ∈ (j', j], arr'[j_] ≥ piv
abbrev Partition.IsPartitioned  [Ord α] (i j : Nat) (pivot : α) (x : Partition α n) :=
  RangeHas n (¬lt pivot  x.arr'[·]) i x.i' ∧ RangeHas n (¬lt x.arr'[·]  pivot) (x.j' + 1) (j + 1)


open Vector

namespace Partition
variable [Ord α]
open Ord
variable (lt_asymm : ∀ {x y : α}, lt x y → ¬lt y x)

include lt_asymm in
private theorem lt_irrefl : ∀ (x : α), ¬lt x x :=
  fun _ h => (lt_asymm h) h


variable (le_trans' : ∀ {x y z : α}, ¬lt y x → ¬lt z y → ¬lt z x)


include lt_asymm in
private theorem hoare.eager.maybeSwap_sorted (as : Vector α n) (low high : Nat) (hlh : low ≤ high) (hn : high < n) : ¬lt (maybeSwap as ⟨low, by omega⟩ ⟨high, by omega⟩)[high] (maybeSwap as ⟨low, by omega⟩ ⟨high, by omega⟩)[low] := by
  unfold maybeSwap; split
  · next h =>
      have _ := lt_asymm h
      simp_all [as.getElem_swap_right, as.getElem_swap_left]
  · assumption



-- set_option trace.profiler true in
private theorem hoare.eager.median_of_three_sorted [Std.TransOrd α] {arr : Vector α n} {left mid right: Nat} (hlm : left ≤ mid) (hmr : mid ≤ right) (hr : right < n) :
  have arr_ := arr
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
    · have : (arr2.swap mid right)[left] = arr2[left] :=
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
          refine le_trans' (lt_asymm ?_) hh1
          assumption
        · assumption



protected theorem hoare.eager.loop.partition_bounds {left right : Nat} {hr : right < n} {pivot : α} {arr : Vector α n} {i j : Nat} {hli : left < i} {hjr : j < right} {hij : i ≤ j + 1} : (loop left right hr pivot arr i j hli hij hjr).val.j' < (loop left right hr pivot arr i j hli hij hjr).val.i' := by
  induction arr, i, j, hli, hij, hjr using loop.induct (hr := hr) (pivot := pivot) with
  | case1 arr i j hli hjr hij hgt =>
    unfold loop; simp [*]
  | case2 arr i j hli hjr hij hgt hh_ne ih =>
    unfold loop; simp [*]
  | case3 arr i j hli hjr hij hgt hh_ne hhne ih =>
    unfold loop; simp [*]
  | case4 arr i j hli hjr hij hgt hh_ne hhne hlt ih =>
    unfold loop; simp [*]
  | case5 arr i j hli hjr hij hgt hh_ne hhne hlt =>
    unfold loop; simp [*]
    omega

protected theorem hoare.eager.partition_bounds {arr : Vector α n} {left : Nat} {right : Nat} {hlr : left < right} {hr : right < n} : (Partition.hoare.eager arr left right hlr hr).val.j' < (Partition.hoare.eager arr left right hlr hr).val.i' := by
  unfold Partition.hoare.eager
  apply Partition.hoare.eager.loop.partition_bounds

protected theorem hoare.eager.loop.permStabilizing {left right : Nat} {hr : right < n} {pivot : α} {arr : Vector α n} {i j : Nat}  {hli : left < i} {hjr : j < right} {hij : i ≤ j + 1} : PermStabilizing' i j (loop left right hr pivot arr i j hli hij hjr).val.arr' arr
:= by
  induction arr, i, j, hli, hij, hjr using hoare.eager.loop.induct (hr := hr) (pivot := pivot)
  all_goals unfold loop; simp [*]
  · case case1 arr i j hli hjr hij hgt =>
    apply PermStabilizing'.refl
  · case case2 arr i j hli hjr hij hgt hh_ne ih =>
    apply PermStabilizing'.mono ih <;> omega
  · case case3 arr i j hli hjr hij hgt hh_ne hhne ih =>
    apply PermStabilizing'.mono ih <;> omega
  · case case4 arr i j hli hjr hij hgt hh_ne hhne hlt ih =>
    apply PermStabilizing'.trans
    · apply PermStabilizing'.mono ih <;> omega
    · apply swap_permStabilizing'; all_goals omega
  · case case5 arr i j hli hjr hij hgt hh_ne hhne hlt =>
    apply PermStabilizing'.refl


protected theorem hoare.eager.permStabilizing {arr : Vector α n} {left : Nat} {right : Nat} {hlr : left < right} {hr : right < n} : PermStabilizing' left right (Partition.hoare.eager arr left right hlr hr).val.arr' arr := by
  apply PermStabilizing'.trans
  · apply PermStabilizing'.mono hoare.eager.loop.permStabilizing <;> omega
  ·
    -- apply sortAt_of_sortAt_of_sortAt_permStabilizing <;> omega
    apply PermStabilizing'.trans
    apply PermStabilizing'.trans
    all_goals apply maybeSwap_permStabilizing
    all_goals simp only; omega


-- private abbrev Partition.IsPartitioned (i j : Nat) (pivot : α) (x : Partition α n) := RangeHas n (¬lt pivot  x.arr'[·]) i x.i' ∧ RangeHas n (¬lt x.arr'[·]  pivot) (x.j' + 1) (j + 1)

-- variable (lt_asymm : ∀ {x y : α}, lt x y → ¬lt y x)

include lt_asymm in
-- protected theorem Partition.loop.sorted {left right : Nat} {hr : right < n} {pivot : α} {arr : Vector α n} {i j : Nat}  {hli : left < i} {hjr : j < right} {hij : i ≤ j + 1} : let x := (Partition.loop left right hr pivot arr i j hli hjr hij).val; RangeHas n (¬lt pivot  x.arr'[·]) i x.i' ∧ RangeHas n (¬lt x.arr'[·] pivot) (x.j' + 1) (j + 1)
protected theorem hoare.eager.loop.sorted {left right : Nat} {hr : right < n} {pivot : α} {arr : Vector α n} {i j : Nat}  {hli : left < i} {hjr : j < right} {hij : i ≤ j + 1} : IsPartitioned i j pivot (Partition.hoare.eager.loop left right hr pivot arr i j hli hij hjr).val
:= by
  -- show Partition.IsPartitioned i j pivot (Partition.loop left right hr pivot arr i j hli hjr hij).val
  induction arr, i, j, hli, hij, hjr using hoare.eager.loop.induct (hr := hr) (pivot := pivot) with
  | case1 arr i j hli hjr hij hgt =>
    unfold loop; simp [*]
    constructor <;> (simp; apply RangeHas.refl)

  | case2 arr i j hli hjr hij hgt hh_ne ih  =>
    unfold loop; simp [*]
    replace hh_ne := lt_asymm hh_ne
    have hi : i < n := by omega

    constructor
    · replace ih := ih.1
      apply RangeHas.prepend (ha := hi) (pred := (¬lt pivot (loop ..).val.arr'[·] = true))
      · simp_all [loop.permStabilizing.2.1]
      · assumption
    · exact ih.2
  | case3 arr i j hli hjr hij hgt hh_ne hhne ih =>
    unfold loop; simp [*]
    replace hhne := lt_asymm hhne
    have hj : j < n := by omega

    constructor
    · exact ih.1
    · have : j - 1 + 1 = j := by omega
      replace ih := ih.2
      rw [this] at ih
      apply RangeHas.append (hb := hj) (pred := (¬lt (loop ..).val.arr'[·] pivot = true))
      · simp_all [loop.permStabilizing.2.2 ⟨j, hj⟩ (by omega : j - 1 < j)]
      · assumption
  | case4 arr i j hli hjr hij hgt hh_ne hhne hlt ih =>
    unfold loop; simp [*]
    have hi : i < n := by omega
    have hj : j < n := by omega

    constructor
    · apply RangeHas.prepend (ha := hi) (pred := (¬lt pivot (loop ..).val.arr'[·] = true))
      · simp_all [loop.permStabilizing.2.1, arr.getElem_swap_left]
      · exact ih.1

    · apply RangeHas.append (hb := hj) (pred := (¬lt (loop ..).val.arr'[·] pivot = true))
      · simp_all [loop.permStabilizing.2.2 ⟨j, hj⟩ (by omega : j - 1 < j), arr.getElem_swap_right]
      · have _ := show j - 1 + 1 = j by omega ▸ ih.2; assumption

  | case5 arr i j hli hjr hij hgt hh_ne hhne hlt =>
    unfold loop; simp [*]
    have heq : i = j := by omega
    have hi : i < n := by omega
    constructor ; all_goals simp
    · simp_all [RangeHas.singular]
    · have : j - 1 + 1 = j + 1 ∨ j - 1 + 1 = j := by omega
      cases this with
      | inl h => simp only [h]; apply RangeHas.refl
      | inr _ => simp_all [RangeHas.singular]

-- variable (le_trans' : ∀ {x y z : α}, ¬lt y x → ¬lt z y → ¬lt z x)

protected theorem hoare.eager.sorted  [Std.TransOrd α] {arr : Vector α n} {left : Nat} {right : Nat} {hlr : left < right} {hr : right < n} : ∃ (pivot : α), IsPartitioned left right pivot (Partition.hoare.eager arr left right hlr hr).val :=

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

  let x : Partition α n := (loop left right hr pivot  arr_ (left + 1) (right - 1) (by omega) (by omega) (by omega)).val
  have : IsPartitioned left right pivot x := by
    have hh1 : IsPartitioned (left + 1) (right - 1) pivot x := hoare.eager.loop.sorted (lt_asymm := lt_asymm)

    have hh2 : ¬lt pivot arr_[left] ∧ ¬lt arr_[right] pivot := hoare.eager.median_of_three_sorted hlm hmr hr

    have : PermStabilizing' (left + 1) (right - 1) x.arr' arr_ := hoare.eager.loop.permStabilizing
    replace hh2 : ¬lt pivot x.arr'[left] ∧ ¬lt x.arr'[right] pivot := by
      have heq_left : x.arr'[left] = arr_[left] := this.2.1 ⟨left, by omega⟩ (by grind)
      have heq_right : x.arr'[right] = arr_[right] := this.2.2 ⟨right, by omega⟩ (by grind)
      rwa [heq_left, heq_right]

    have hh1_right : RangeHas n (¬lt x.arr'[·]  pivot) (x.j' + 1) right := by
      have : right - 1 + 1 = right := by omega
      rw [←this]; exact hh1.right
    exact ⟨RangeHas.prepend (ha := by omega) hh2.left hh1.left , RangeHas.append (hb := by omega) hh2.right hh1_right⟩
  ⟨pivot, this⟩

end Partition




open Vector

namespace Partition
variable [Ord α]




theorem hoare.classic.while_i_elem_not_left_of_piv {arr : Vector α n} {harltp : ¬lt arr[right] pivot}
  : ¬lt arr[(hoare.classic.loop.while_i left right hr pivot arr i j hjr harltp ival hii hxi).1.val] pivot := by
  induction ival, hii, hxi using hoare.classic.loop.while_i.induct right hr pivot arr i j harltp with
  | case1 ival hii hxi hi hlt hir ih =>
    unfold hoare.classic.loop.while_i; simp [*]
  | case2 ival hii hxi hi hle =>
    unfold hoare.classic.loop.while_i; simp [*]


theorem hoare.classic.while_j_elem_not_right_of_piv {arr : Vector α n} {halgep : ¬lt pivot arr[left]} :
  ¬lt pivot arr[(hoare.classic.loop.while_j left right hr hl pivot arr i j hjr hli halgep   jval hxj hjj).1.val] := by
  induction jval, hxj, hjj using hoare.classic.loop.while_j.induct left right hr hl pivot arr i j hjr halgep with
  | case1 jval hxj hjj hj hlt hjl ih =>
    unfold hoare.classic.loop.while_j; simp [*]
  | case2 jval hxj hjj hj  hle =>
    unfold hoare.classic.loop.while_j; simp [*]




theorem hoare.classic.while_i_before_is_left {arr : Vector α n} {harltp : ¬lt arr[right] pivot} :
  RangeHas n (lt arr[·] pivot) ival (hoare.classic.loop.while_i left right hr pivot arr i j hjr harltp ival hii hxi) := by
  induction ival, hii, hxi using hoare.classic.loop.while_i.induct right hr pivot arr i j harltp with
  | case1 ival hii hxi hi hlt hir ih =>
    unfold hoare.classic.loop.while_i; simp [*]
    apply RangeHas.prepend <;> grind [Ordering.isLT]
  | case2 ival hii hxi hi hle =>
    unfold hoare.classic.loop.while_i; simp [*]
    apply RangeHas.refl


theorem hoare.classic.while_j_before_is_right {arr : Vector α n} {halgep : ¬lt pivot arr[left]} :
  RangeHas n (lt pivot arr[·]) ((hoare.classic.loop.while_j left right hr hl pivot arr i j hjr hli halgep   jval hxj hjj) + 1) (jval + 1) := by
  induction jval, hxj, hjj using hoare.classic.loop.while_j.induct left right hr hl pivot arr i j hjr halgep with
  | case1 jval hxj hjj hj hlt hjl ih =>
    unfold hoare.classic.loop.while_j; simp [*]
    replace ih := show (jval - 1 + 1) = jval by omega ▸ ih
    apply RangeHas.append <;> grind [Ordering.isLT]
  | case2 jval hxj hjj hj  hle =>
    unfold hoare.classic.loop.while_j; simp [*]
    apply RangeHas.refl

-- #check Partition.hoare.classic.loop.induct
theorem hoare.classic.loop.partition_bounds {left right : Nat} {hr : right < n} {hl : left < n} {pivot : α} {arr : Vector α n} {i j : Nat} {hli : left < i} {hij : i ≤ j + 1} {hjr : j < right} {halgep : ¬lt pivot arr[left]} {harltp : ¬lt arr[right] pivot} : (loop left right hr hl pivot arr i j hli hij hjr halgep harltp).val.j' < (loop left right hr hl pivot arr i j hli hij hjr halgep harltp).val.i' := by
  induction arr, i, j, hli, hij, hjr, halgep, harltp using loop.induct left right hr hl pivot; all_goals unfold loop; simp [*]
  · case  case1 arr i j hli hij hjr halgep harltp i' hi1' hi2' heq_i' j' hj' heq_j' hlt arr' halgep' harltp' ih =>
    -- unfold loop; simp [*]
    trivial
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

section lt_asymm
variable (lt_asymm : ∀ {x y : α}, lt x y → ¬lt y x)



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
        have := show (arr.swap i' j')[k] = _ by
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
        have := show (arr.swap i' j')[k] = _ by
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
end lt_asymm


open Ord
variable [Std.TransOrd α]
private theorem hoare.classic.median_of_three_sorted {arr : Vector α n} {left mid right: Nat} (hlm : left ≤ mid) (hmr : mid ≤ right) (hr : right < n) :
  have arr_ := arr
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
          refine le_trans' (lt_asymm ?_) hh1
          assumption
        · assumption


protected theorem hoare.classic.partition_bounds' {arr : Vector α n} {left : Nat} {right : Nat} {hlr : left < right} {hr : right < n} : (hoare.classic arr left right hlr hr).val.j' < (hoare.classic arr left right hlr hr).val.i' := by
  unfold hoare.classic
  apply Partition.hoare.classic.loop.partition_bounds


protected theorem hoare.classic.permStabilizing' {arr : Vector α n} {left : Nat} {right : Nat} {hlr : left < right} {hr : right < n} : PermStabilizing' left right (hoare.classic arr left right hlr hr).val.arr' arr := by
  apply PermStabilizing'.trans
  · apply PermStabilizing'.mono hoare.classic.loop.permStabilizing <;> omega
  · apply PermStabilizing'.trans
    apply PermStabilizing'.trans
    all_goals apply maybeSwap_permStabilizing
    all_goals simp only; omega


protected theorem hoare.classic.sorted (arr : Vector α n) {left : Nat} {right : Nat} (hlr : left < right) (hr : right < n) : ∃ (pivot : α), IsPartitioned left right pivot (hoare.classic arr left right hlr hr).val :=

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

  have hh2 : ¬lt pivot arr_[left] ∧ ¬lt arr_[right] pivot := hoare.classic.median_of_three_sorted hlm hmr hr
  let x : Partition α n := (hoare.classic.loop left right hr (by omega) pivot  arr_ (left + 1) (right - 1) (by omega) (by omega) (by omega) hh2.left hh2.right).val

  have : IsPartitioned left right pivot x := by
    have hh1 : IsPartitioned (left + 1) (right - 1) pivot x := hoare.classic.loop.sorted (lt_asymm := lt_asymm)

    have : PermStabilizing' (left + 1) (right - 1) x.arr' arr_ := hoare.classic.loop.permStabilizing
    replace hh2 : ¬lt pivot x.arr'[left] ∧ ¬lt x.arr'[right] pivot := by
      have heq_left : x.arr'[left] = arr_[left] := this.2.1 ⟨left, by omega⟩ (by grind)
      have heq_right : x.arr'[right] = arr_[right] := this.2.2 ⟨right, by omega⟩ (by grind)
      rwa [heq_left, heq_right]

    have hh1_right : RangeHas n (¬lt x.arr'[·]  pivot) (x.j' + 1) right := by
      have : right - 1 + 1 = right := by omega
      rw [←this]; exact hh1.right
    exact ⟨RangeHas.prepend (ha := by omega) hh2.left hh1.left , RangeHas.append (hb := by omega) hh2.right hh1_right⟩
  ⟨pivot, this⟩
end Partition

namespace Partition
variable [Ord α]

protected theorem hoare.partition_bounds {arr : Vector α n} {left : Nat} {right : Nat} {hlr : left < right} {hr : right < n} : (Partition.hoare arr left right hlr hr).val.j' < (Partition.hoare arr left right hlr hr).val.i' := by
  unfold Partition.hoare; simp [*]; split
  · apply hoare.classic.loop.partition_bounds
  · apply hoare.eager.partition_bounds; assumption

protected theorem hoare.permStabilizing {arr : Vector α n} {left : Nat} {right : Nat} {hlr : left < right} {hr : right < n} : PermStabilizing' left right (Partition.hoare arr left right hlr hr).val.arr' arr := by
  unfold Partition.hoare; simp [*]; split
  · apply PermStabilizing'.trans
    · apply PermStabilizing'.mono hoare.classic.loop.permStabilizing <;> omega
    · apply PermStabilizing'.trans
      apply PermStabilizing'.trans
      all_goals apply maybeSwap_permStabilizing
      all_goals simp only; omega
  · apply hoare.eager.permStabilizing; assumption

protected theorem hoare.sorted [Std.TransOrd α] (arr : Vector α n) {left : Nat} {right : Nat} (hlr : left < right) (hr : right < n) : ∃ (pivot : α), IsPartitioned left right pivot (Partition.hoare arr left right hlr hr).val := by
  unfold Partition.hoare; simp [*]; split
  · apply hoare.classic.sorted <;> grind
  · apply hoare.eager.sorted <;> grind
end Partition

open Vector


section qsort_hoare

open Partition
open Array

variable [Ord α]

open Ord

theorem qsort_hoare.sort.permStabilizing {as : Vector α n} {left right : Nat} {hsize' : right ≤ n - 1} : Vector.PermStabilizing' left right (sort as left right hsize') as := by
  induction as, left, right, hsize' using qsort_hoare.sort.induct with
  | case1 as left right hsize' hlr as' j' i' hli hjr heq as'' ih1 _ih1 ih2 =>
    unfold sort; simp [*]

    have ih0 := heq ▸ hoare.permStabilizing
    replace ih1 : Vector.PermStabilizing' left right .. := ih1.mono (by omega) (by omega)
    replace ih2 : Vector.PermStabilizing' left right .. := ih2.mono (by omega) (by omega)

    exact ih2 |>.trans ih1 |>.trans ih0
  | case2 as left right hsize' hlr =>
    unfold sort; simp [*]
    apply Vector.PermStabilizing'.refl

theorem qsort_hoare.perm' {as : Array α} {left : Nat} {right : Nat}  : (qsort_hoare as left right).Perm as := by
  simp only [qsort_hoare]; split
  any_goals simp only [panicWithPosWithDecl, panic, panicCore, *]
  all_goals
  have := qsort_hoare.sort.permStabilizing (as := Vector.mk as rfl) (left := left) (hsize' := by solve_by_elim) |>.1
  grind [Vector.Perm]


theorem qsort_hoare.perm {as : Array α} : (qsort_hoare as).Perm as := qsort_hoare.perm'


@[simp]
theorem qsort_hoare.qs_size {as : Array α} :
    (qsort_hoare as left right).size = as.size := qsort_hoare.perm'.size_eq

variable [Std.TransOrd α]
theorem qsort_hoare.sort.monotonic {as : Vector α n} {hsize' : right ≤ n - 1} : let q := (sort as left right hsize'); ∀ (i j : Fin n), (left ≤ i) → (i < j) → (j ≤ right) → ¬lt q[j] q[i] := by
  induction as, left, right, hsize' using qsort_hoare.sort.induct with
  | case1 as left right hsize' hlr as' j' i' hli' hjr' heq as'' ih1 _ih1 ih2 =>
    unfold sort; simp only [↓reduceDIte, hlr, heq]

    intro i j hli hij hjr; exact

    have hji' : j' < i' := by apply heq
      ▸ hoare.partition_bounds
    let as''' := sort as'' i' right (by omega)

    if hhi : i' ≤ i then by
      apply ih2 <;> assumption
    else if hhj : j ≤ j' then by
      rw [qsort_hoare.sort.permStabilizing.2.left j (by omega), qsort_hoare.sort.permStabilizing.2.left i (by omega)]
      apply ih1 <;> assumption
    else by
      replace hhi : i < i' := by omega
      replace hhj : j' < j := by omega

      have ⟨pivot, ih0⟩ := hoare.sorted as hlr (by omega)
      -- ih0 : Partitioned left right pivot (part as left right hlr hr).val

      replace ih0 :
          (∀ (i : Fin n), left ≤ i → i < i' → ¬lt pivot as'[i]) ∧
          (∀ (j : Fin n), j' + 1 ≤ j → j < right + 1 → ¬lt as'[j] pivot) := by
        unfold Partition.IsPartitioned at ih0; rwa [heq] at ih0

      have hhh1 : ¬lt pivot as'''[i] :=
        suffices ¬lt pivot as''[i] by rwa [qsort_hoare.sort.permStabilizing.2.left i (by omega)]
        if _ : i ≤ j' then by
          apply Vector.PermStabilizing'.invariance (motive := (¬lt pivot ·)) (left := left) (hi := j' + 1) (hperm := qsort_hoare.sort.permStabilizing) (h := ?_ )
          any_goals omega
          · intro i_ _ _
            apply ih0.left i_ <;> omega
        else by
          rw [qsort_hoare.sort.permStabilizing.2.right _ ?_]
          apply ih0.left i
          all_goals omega

      have hhh2 : ¬lt as'''[j] pivot :=
        if _ : i' ≤ j then by
          apply Vector.PermStabilizing'.invariance (motive := (¬lt · pivot)) (left := i') (hi := right + 1) (hperm := qsort_hoare.sort.permStabilizing) (h := ?_)
          any_goals omega
          · intro j_ _ _
            rw [qsort_hoare.sort.permStabilizing.2.right j_ (by omega)]
            apply ih0.right j_ <;> omega
        else by
          rw [qsort_hoare.sort.permStabilizing.2.left _ ?_, qsort_hoare.sort.permStabilizing.2.right _ ?_]
          apply ih0.right j
          all_goals omega
      exact le_trans' hhh1 hhh2
  | case2 => omega

theorem qsort_hoare.monotonic' {as : Array α} {left : Nat} {right : Nat} :  let q := (qsort_hoare as left right); ∀ (i j : Fin q.size), (left ≤ i) → (i < j) → (j ≤ right) → ¬lt q[j] q[i] := by
  simp only
  intro  i j _ _ _
  have _ : j.cast qsort_hoare.qs_size ≤ as.size - 1 := by omega
  simp only [qsort_hoare]; split
  any_goals simp only [panicWithPosWithDecl, panic, panicCore, *]
  all_goals apply qsort_hoare.sort.monotonic (i.cast qsort_hoare.qs_size) (j.cast qsort_hoare.qs_size) <;> assumption

theorem qsort_hoare.monotonic {as : Array α} : ∀ (i j : Fin (qsort_hoare as).size), i < j → ¬lt (qsort_hoare as)[j] (qsort_hoare as)[i] := by
  intro i j h
  apply qsort_hoare.monotonic'
  · omega
  · exact h
  · have := j.2; simp only [qsort_hoare.qs_size] at this; omega



end qsort_hoare

section qsort_strict_hoare

open Partition
open Array

variable [Ord α]
variable [Std.TransOrd α]
open Ord

theorem qsort_hoare_strict.sort.permStabilizing {as : Vector α n} {left right : Nat} {hsize' : right ≤ n - 1} : Vector.PermStabilizing' left right (sort as left right hsize') as := by
  induction as, left, right, hsize' using qsort_hoare_strict.sort.induct with
  | case1 as left right hsize' hlr as' j' i' hli hjr heq as'' ih1 _ih1 ih2 =>
    unfold sort; simp [*]

    have ih0 := heq ▸ hoare.classic.permStabilizing'
    replace ih1 : Vector.PermStabilizing' left right .. := ih1.mono (by omega) (by omega)
    replace ih2 : Vector.PermStabilizing' left right .. := ih2.mono (by omega) (by omega)

    exact ih2 |>.trans ih1 |>.trans ih0
  | case2 as left right hsize' hlr =>
    unfold sort; simp [*]
    apply Vector.PermStabilizing'.refl

theorem qsort_hoare_strict.perm' {as : Array α} {left : Nat} {right : Nat}  : (qsort_hoare_strict as left right).Perm as := by
  simp only [qsort_hoare_strict]; split
  any_goals simp only [panicWithPosWithDecl, panic, panicCore, *]
  all_goals
  have := qsort_hoare_strict.sort.permStabilizing (as := Vector.mk as rfl) (left := left) (hsize' := by solve_by_elim) |>.1
  grind [Vector.Perm]


theorem qsort_hoare_strict.perm {as : Array α} : (qsort_hoare_strict as).Perm as := qsort_hoare_strict.perm'


@[simp]
theorem qsort_hoare_strict.qs_size {as : Array α} :
    (qsort_hoare_strict as left right).size = as.size := qsort_hoare_strict.perm'.size_eq

theorem qsort_hoare_strict.sort.monotonic {as : Vector α n} {hsize' : right ≤ n - 1} : let q := (sort as left right hsize'); ∀ (i j : Fin n), (left ≤ i) → (i < j) → (j ≤ right) → ¬lt q[j] q[i] := by
  induction as, left, right, hsize' using qsort_hoare_strict.sort.induct with
  | case1 as left right hsize' hlr as' j' i' hli' hjr' heq as'' ih1 _ih1 ih2 =>
    unfold sort; simp only [↓reduceDIte, hlr, heq]

    intro i j hli hij hjr; exact


    have hji' : j' < i' := by apply heq
      ▸ hoare.classic.partition_bounds'
    let as''' := sort as'' i' right (by omega)

    if hhi : i' ≤ i then by
      apply ih2 <;> assumption
    else if hhj : j ≤ j' then by
      rw [qsort_hoare_strict.sort.permStabilizing.2.left j (by omega), qsort_hoare_strict.sort.permStabilizing.2.left i (by omega)]
      apply ih1 <;> assumption
    else by
      replace hhi : i < i' := by omega
      replace hhj : j' < j := by omega

      have ⟨pivot, ih0⟩ := hoare.classic.sorted as hlr (by omega)
      -- ih0 : Partitioned left right pivot (part as left right hlr hr).val

      replace ih0 :
          (∀ (i : Fin n), left ≤ i → i < i' → ¬lt pivot as'[i]) ∧
          (∀ (j : Fin n), j' + 1 ≤ j → j < right + 1 → ¬lt as'[j] pivot) := by
        unfold Partition.IsPartitioned at ih0; rwa [heq] at ih0

      have hhh1 : ¬lt pivot as'''[i] :=
        suffices ¬lt pivot as''[i] by rwa [qsort_hoare_strict.sort.permStabilizing.2.left i (by omega)]
        if _ : i ≤ j' then by
          apply Vector.PermStabilizing'.invariance (motive := (¬lt pivot ·)) (left := left) (hi := j' + 1) (hperm := qsort_hoare_strict.sort.permStabilizing) (h := ?_ )
          any_goals omega
          · intro i_ _ _
            apply ih0.left i_ <;> omega
        else by
          rw [qsort_hoare_strict.sort.permStabilizing.2.right _ ?_]
          apply ih0.left i
          all_goals omega

      have hhh2 : ¬lt as'''[j] pivot :=
        if _ : i' ≤ j then by
          apply Vector.PermStabilizing'.invariance (motive := (¬lt · pivot)) (left := i') (hi := right + 1) (hperm := qsort_hoare_strict.sort.permStabilizing) (h := ?_)
          any_goals omega
          · intro j_ _ _
            rw [qsort_hoare_strict.sort.permStabilizing.2.right j_ (by omega)]
            apply ih0.right j_ <;> omega
        else by
          rw [qsort_hoare_strict.sort.permStabilizing.2.left _ ?_, qsort_hoare_strict.sort.permStabilizing.2.right _ ?_]
          apply ih0.right j
          all_goals omega
      exact le_trans' hhh1 hhh2
  | case2 => omega

theorem qsort_hoare_strict.monotonic' {as : Array α} {left : Nat} {right : Nat} :  let q := (qsort_hoare_strict as left right); ∀ (i j : Fin q.size), (left ≤ i) → (i < j) → (j ≤ right) → ¬lt q[j] q[i] := by
  simp only
  intro  i j _ _ _
  have _ : j.cast qsort_hoare_strict.qs_size ≤ as.size - 1 := by omega
  simp only [qsort_hoare_strict]; split
  any_goals simp only [panicWithPosWithDecl, panic, panicCore, *]
  all_goals apply qsort_hoare_strict.sort.monotonic (i.cast qsort_hoare_strict.qs_size) (j.cast qsort_hoare_strict.qs_size) <;> assumption

theorem qsort_hoare_strict.monotonic {as : Array α} : ∀ (i j : Fin (qsort_hoare_strict as).size), i < j → ¬lt (qsort_hoare_strict as)[j] (qsort_hoare_strict as)[i] := by
  intro i j h
  apply qsort_hoare_strict.monotonic'
  · omega
  · exact h
  · have := j.2; simp only [qsort_hoare_strict.qs_size] at this; omega



end qsort_strict_hoare
