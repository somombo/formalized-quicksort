import Quicksort.Defs
import Quicksort.Utils.RangeHas
import Quicksort.Utils.PermStabalizing

open Batteries Batteries.Vector

variable [Ord α]

section init
variable (lt_asymm : ∀ {x y : α}, lt x y → ¬lt y x)

include lt_asymm in
theorem lt_irrefl : ∀ (x : α), ¬lt x x :=
  fun _ h => (lt_asymm h) h


variable (le_trans : ∀ {x y z : α}, ¬lt y x → ¬lt z y → ¬lt z x)



theorem sortAt_permStabilizing (as : Vector α n) (low high : Nat) (hlh : low ≤ high) (hn : high < n) :  PermStabilizing' low high (sortAt as low high hlh hn) as  := by
  unfold sortAt
  split
  · apply swap_permStabilizing' <;> all_goals simp <;> assumption
  · rfl


theorem sortAt_of_sortAt_of_sortAt_permStabilizing {arr : Vector α n} {left mid right: Nat} (hlm : left ≤ mid) (hmr : mid ≤ right) (hr : right < n) :
  arr
    |> (sortAt · left mid hlm (by omega))
    |> (sortAt · left right (by omega) hr)
    |> (sortAt · mid right hmr hr)
    |> (PermStabilizing' left right · arr)
  := by
  have hm : mid < n := by omega
  have hlr' : left ≤ right := by omega

  have _ : PermStabilizing' left right .. := sortAt_permStabilizing arr left mid hlm hm |> (PermStabilizing'.mono · Nat.le.refl hmr)
  have _ : PermStabilizing' left right .. := sortAt arr left mid hlm hm
    |> (sortAt_permStabilizing · left right hlr' hr)
  have _ : PermStabilizing' left right .. := sortAt arr left mid hlm hm
    |> (sortAt · left right hlr' hr)
    |> (sortAt_permStabilizing · mid right hmr hr)
    |> (PermStabilizing'.mono · hlm Nat.le.refl)

  apply PermStabilizing'.trans
  apply PermStabilizing'.trans
  repeat assumption


include lt_asymm in
theorem sortAt_sorted (as : Vector α n) (low high : Nat) (hlh : low ≤ high) (hn : high < n) : ¬ (lt (sortAt as low high hlh hn)[high] (sortAt as low high hlh hn)[low]) := by
  unfold sortAt
  split
  · next h =>
      have _ := lt_asymm h
      simp_all [as.getElem_swap_right, as.getElem_swap_left]
  · assumption

-- set_option trace.profiler true in
include lt_asymm in
include le_trans in
theorem sortAt_of_sortAt_of_sortAt_sorted {arr : Vector α n} {left mid right: Nat} (hlm : left ≤ mid) (hmr : mid ≤ right) (hr : right < n) :
  let_fun arr_ := arr
    |> (sortAt · left mid hlm (by omega))
    |> (sortAt · left right (by omega) hr)
    |> (sortAt · mid right hmr hr)
-- ∀ {k_ : Nat} (_ : left ≤ k_) (_ : k_ ≤ right),
  ¬lt arr_[mid] arr_[left] ∧ ¬lt arr_[right] arr_[mid]
  :=
  have _ : left < n := by omega
  have _ : mid < n := by omega

  let arr1 : Vector α n := sortAt arr left mid _ _
  let arr2 : Vector α n := sortAt arr1 left right _ _
  let arr_ : Vector α n := sortAt arr2 mid right _ _

  have hh1 : ¬lt arr1[mid] arr1[left] := sortAt_sorted lt_asymm arr left mid _ _
  have hh2 : ¬lt arr2[right] arr2[left] := sortAt_sorted lt_asymm arr1 left right _ _
  have hh_ : ¬lt arr_[right] arr_[mid] := sortAt_sorted lt_asymm arr2 mid right _ _

  suffices ¬lt arr_[mid] arr_[left] from ⟨this, hh_⟩

  if hleqm : left = mid then by
    simp only [hleqm]
    exact lt_irrefl lt_asymm arr_[mid]
  else by
    have hlneqr : left ≠ right := by omega
    simp only [arr_]
    unfold sortAt
    split
    · have : (arr2.swap ⟨mid, ‹_›⟩ ⟨right, ‹_›⟩)[left] = _ :=
        arr2.getElem_swap_of_ne _ hleqm hlneqr
      simp only [this, arr2.getElem_swap_left, Fin.getElem_fin]
      assumption
    · exact
      if hmeql : mid = left then by
        simp only [hmeql]
        exact lt_irrefl lt_asymm arr2[left]

      else if hmeqr : mid = right then by
        simp only [hmeqr]
        exact hh2
      else by
        simp only [arr2]
        unfold sortAt
        split

        · have : (arr1.swap ⟨left, by omega⟩ ⟨right, hr⟩)[mid] = _ :=
            arr1.getElem_swap_of_ne (_ : mid < n) hmeql hmeqr
          simp only [this, arr1.getElem_swap_left, Fin.getElem_fin]
          refine le_trans (lt_asymm ?_) hh1
          assumption
        · assumption


abbrev Partitioned (i j : Nat) (pivot : α) (x : Partition α n) :=
  RangeHas n (¬lt pivot  x.arr'[·]) i x.i' ∧ RangeHas n (¬lt x.arr'[·]  pivot) (x.j' + 1) (j + 1)

end init

namespace hoare

protected theorem partition.loop.partition_bounds {left right : Nat} {hr : right < n} {pivot : α} {arr : Vector α n} {i j : Nat} {hli : left < i} {hjr : j < right} {hij : i ≤ j + 1} : (loop left right hr pivot arr i j hli hjr hij).val.j' < (loop left right hr pivot arr i j hli hjr hij).val.i' := by
  induction arr, i, j, hli, hjr, hij using partition.loop.induct (hr := hr) (pivot := pivot) with
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

protected theorem partition.partition_bounds {arr : Vector α n} {left : Nat} {right : Nat} {hlr : left < right} {hr : right < n} : (partition arr left right hlr hr).val.j' < (partition arr left right hlr hr).val.i' := by
  simp only [partition]
  apply partition.loop.partition_bounds

protected theorem partition.loop.permStabilizing {left right : Nat} {hr : right < n} {pivot : α} {arr : Vector α n} {i j : Nat}  {hli : left < i} {hjr : j < right} {hij : i ≤ j + 1} : PermStabilizing' i j (loop left right hr pivot arr i j hli hjr hij).val.arr' arr
:= by
  induction arr, i, j, hli, hjr, hij using partition.loop.induct (hr := hr) (pivot := pivot) with
  | case1 arr i j hli hjr hij hgt =>
    unfold loop; simp [*]
    apply PermStabilizing'.refl
  | case2 arr i j hli hjr hij hgt hh_ne ih =>
    unfold loop; simp [*]
    apply PermStabilizing'.mono ih <;> omega
  | case3 arr i j hli hjr hij hgt hh_ne hhne ih =>
    unfold loop; simp [*]
    apply PermStabilizing'.mono ih <;> omega
  | case4 arr i j hli hjr hij hgt hh_ne hhne hlt ih =>
    unfold loop; simp [*]
    apply PermStabilizing'.trans
    · apply PermStabilizing'.mono ih <;> omega
    · apply swap_permStabilizing' <;>  simp <;> omega
  | case5 arr i j hli hjr hij hgt hh_ne hhne hlt =>
    unfold loop; simp [*]
    apply PermStabilizing'.refl


protected theorem partition.permStabilizing {arr : Vector α n} {left : Nat} {right : Nat} {hlr : left < right} {hr : right < n} : PermStabilizing' left right (partition arr left right hlr hr).val.arr' arr := by
  apply PermStabilizing'.trans
  · apply PermStabilizing'.mono partition.loop.permStabilizing <;> simp_arith
  · apply sortAt_of_sortAt_of_sortAt_permStabilizing

-- private abbrev Partitioned (i j : Nat) (pivot : α) (x : Partition α n) := RangeHas n (¬lt pivot  x.arr'[·]) i x.i' ∧ RangeHas n (¬lt x.arr'[·]  pivot) (x.j' + 1) (j + 1)

variable (lt_asymm : ∀ {x y : α}, lt x y → ¬lt y x)

include lt_asymm in
-- protected theorem partition.loop.sorted {left right : Nat} {hr : right < n} {pivot : α} {arr : Vector α n} {i j : Nat}  {hli : left < i} {hjr : j < right} {hij : i ≤ j + 1} : let x := (partition.loop left right hr pivot arr i j hli hjr hij).val; RangeHas n (¬lt pivot  x.arr'[·]) i x.i' ∧ RangeHas n (¬lt x.arr'[·] pivot) (x.j' + 1) (j + 1)
protected theorem partition.loop.sorted {left right : Nat} {hr : right < n} {pivot : α} {arr : Vector α n} {i j : Nat}  {hli : left < i} {hjr : j < right} {hij : i ≤ j + 1} : Partitioned i j pivot (partition.loop left right hr pivot arr i j hli hjr hij).val
:= by
  -- show Partitioned i j pivot (partition.loop left right hr pivot arr i j hli hjr hij).val
  induction arr, i, j, hli, hjr, hij using partition.loop.induct (hr := hr) (pivot := pivot) with
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
    · simp_all only [RangeHas.singular]
    · have : j - 1 + 1 = j + 1 ∨ j - 1 + 1 = j := by omega
      cases this with
      | inl h => simp only [h]; apply RangeHas.refl
      | inr _ => simp_all only [RangeHas.singular]

variable (le_trans : ∀ {x y z : α}, ¬lt y x → ¬lt z y → ¬lt z x)

include le_trans in
include lt_asymm in
protected theorem partition.sorted {arr : Vector α n} {left : Nat} {right : Nat} {hlr : left < right} {hr : right < n} : ∃ (pivot : α), Partitioned left right pivot (partition arr left right hlr hr).val :=

  let mid := left + ((right - left)/2)
  have hlm : left ≤ mid := Nat.le_add_right left ((right - left) / 2)
  have hlr_ :  left ≤ right := Nat.le_of_succ_le hlr
  have hmr :  mid ≤ right :=
    have : ((right - left)/2) ≤ right-left := Nat.div_le_self (right - left) 2
    have : left + ((right - left)/2) ≤ left + (right - left) := Nat.add_le_add_left this left
    Trans.trans this (Nat.add_sub_of_le hlr_)
  have hm :  mid < n := Trans.trans hmr hr

  let arr_ := arr |> (sortAt · left mid hlm hm) |> (sortAt · left right hlr_ hr) |> (sortAt · mid right hmr hr)
  let pivot := arr_[mid]

  let x : Partition α n := (partition.loop left right hr pivot  arr_ (left + 1) (right - 1) (by omega) (by omega) (by omega)).val
  have : Partitioned left right pivot x := by
    have hh1 : Partitioned (left + 1) (right - 1) pivot x := partition.loop.sorted (lt_asymm := lt_asymm)

    have hh2 : ¬lt pivot arr_[left] ∧ ¬lt arr_[right] pivot := sortAt_of_sortAt_of_sortAt_sorted (lt_asymm := lt_asymm) (le_trans := le_trans) hlm hmr hr

    have : PermStabilizing' (left + 1) (right - 1) x.arr' arr_ := partition.loop.permStabilizing
    replace hh2 : ¬lt pivot x.arr'[left] ∧ ¬lt x.arr'[right] pivot := by
      have heq_left : x.arr'[left] = arr_[left] := this.2.1 ⟨left, by omega⟩ (by simp_arith)
      have heq_right : x.arr'[right] = arr_[right] := this.2.2 ⟨right, by omega⟩ (by simp_arith; omega)
      rwa [heq_left, heq_right]

    have hh1_right : RangeHas n (¬lt x.arr'[·]  pivot) (x.j' + 1) right := by
      have : right - 1 + 1 = right := by omega
      rw [←this]; exact hh1.right
    exact ⟨RangeHas.prepend (ha := by omega) hh2.left hh1.left , RangeHas.append (hb := by omega) hh2.right hh1_right⟩
  ⟨pivot, this⟩

end hoare




namespace lomuto

protected theorem partition.loop.partition_bounds {left right : Nat}  {hr : right < n} {pivot : α} {arr : Vector α n} {i j : Nat} {hli : left < i} {hij :  i ≤ j} {hjr : j ≤ right} : (loop left right hr pivot arr i j hli hij hjr).val.j' < (loop left right hr pivot arr i j hli hij hjr).val.i' := by
  induction arr, i, j, hli, hij, hjr using partition.loop.induct (hr := hr) (pivot := pivot)  with
  | case1 arr i j hli hij hjr' i_fin hjr hhlt ih  =>
    unfold loop; simp [*]
  | case2 arr i j hli hij hjr' hjr hhle ih =>
    unfold loop; simp [*]
  | case3 arr i j hli hij hjr' hjr =>
    unfold loop; simp [*]
    omega

protected theorem partition.partition_bounds {arr : Vector α n} {left : Nat} {right : Nat} {hlr : left < right} {hr : right < n} : (partition arr left right hlr hr).val.j' < (partition arr left right hlr hr).val.i' := by
  simp only [partition]
  apply partition.loop.partition_bounds

protected theorem partition.loop.permStabilizing {left right : Nat} {hr : right < n} {pivot : α} {arr : Vector α n} {i j : Nat} {hli : left < i} {hij :  i ≤ j} {hjr : j ≤ right} : PermStabilizing' i right (loop left right hr pivot arr i j hli hij hjr).val.arr' arr
:= by
  induction arr, i, j, hli, hij, hjr using partition.loop.induct (hr := hr) (pivot := pivot) with
  | case1 arr i j hli hij hjr' i_fin hjr hhlt ih  =>
    unfold loop; simp [*]

    apply PermStabilizing'.trans
    · apply PermStabilizing'.mono ih <;> omega
    · apply swap_permStabilizing' <;>  simp <;> omega
  | case2 arr i j hli hij hjr' hjr hhle ih =>
    unfold loop; simp [*]

  | case3 arr i j hli hij hjr' hjr =>
    unfold loop; simp [*]
    have : (⟨right, hr⟩) = (⟨j, by omega⟩ : Fin n) := by simp; omega

    rw [this]
    apply swap_permStabilizing'
    all_goals simp only [Nat.le_refl]
    all_goals omega

protected theorem partition.permStabilizing {arr : Vector α n} {left : Nat} {right : Nat} {hlr : left < right} {hr : right < n} : PermStabilizing' left right (partition arr left right hlr hr).val.arr' arr := by
  apply PermStabilizing'.trans
  · apply PermStabilizing'.mono partition.loop.permStabilizing <;> omega
  · apply sortAt_of_sortAt_of_sortAt_permStabilizing

attribute [-simp] Bool.not_eq_true

private theorem _root_.Batteries.Vector.inclusive_swap {arr : Vector α n} {i j : Nat} {hi : i < n} {hj : j < n} (hij' : i < j) : RangeHas n (¬lt (arr.swap ⟨i, hi⟩ ⟨j, hj⟩)[·] pivot) (i + 1) (j + 1) ↔ RangeHas n (¬lt arr[·] pivot) i j := by
  let arr' := arr.swap ⟨i, hi⟩ ⟨j, hj⟩
  constructor; all_goals intro hif
  · have := RangeHas.unappend hij' hif (hb := hj)
    apply RangeHas.prepend (ha := hi) (pred := (¬lt _[·] _ = _))
    · simp only [Fin.getElem_fin, arr.getElem_swap_right] at this
      exact this.2
    · intro p _ _
      simp only [Fin.getElem_fin,
        ←show arr'[p] = _ by
          apply arr.getElem_swap_of_ne; all_goals simp; omega]
      apply this.1; all_goals omega
  · have := RangeHas.unprepend hij' hif (ha := hi) (pred := (¬lt _[·] _ = _))
    apply RangeHas.append (hb := hj) (pred := (¬lt _[·] _ = _))
    · simp only [Fin.getElem_fin, arr.getElem_swap_right]
      exact this.1
    · intro p _ _
      simp only [Fin.getElem_fin,
        show arr'[p] = _ by
          apply arr.getElem_swap_of_ne; all_goals simp; omega]
      apply this.2; all_goals omega

section split_ih
variable {a b p q : Prop} (ih : a → b → c → p ∧ q) include ih
private theorem _root_.split_ih_left : a → b → c → p := (ih · · · |>.left)
private theorem _root_.split_ih_right :  a → b → c → q := (ih · · · |>.right)
end split_ih

variable (lt_asymm : ∀ {x y : α}, lt x y → ¬lt y x)

include lt_asymm in
-- protected theorem partition.loop.sorted {left right : Nat} {hr : right < n} {pivot : α} {arr : Vector α n} {i j : Nat} {hli : left < i} {hij :  i ≤ j} {hjr : j ≤ right} (hxij : i < j → RangeHas n (¬lt arr[·] pivot) i j ) (hxr : ¬lt arr[right] pivot) (hxr' : ¬lt pivot arr[right]) : let x := (loop left right hr pivot arr i j hli hij hjr).val; RangeHas n (¬lt pivot x.arr'[·]) i x.i' ∧  RangeHas n (¬lt x.arr'[·] pivot) (x.j' + 1) (right + 1) := by
protected theorem partition.loop.sorted {left right : Nat} {hr : right < n} {pivot : α} {arr : Vector α n} {i j : Nat} {hli : left < i} {hij :  i ≤ j} {hjr : j ≤ right} (hxij : i < j → RangeHas n (¬lt arr[·] pivot) i j ) (hxr : ¬lt arr[right] pivot) (hxr' : ¬lt pivot arr[right]) : Partitioned i right pivot (loop left right hr pivot arr i j hli hij hjr).val := by

  induction arr, i, j, hli, hij, hjr using partition.loop.induct (hr := hr) (pivot := pivot) with
  | case1 arr i j hli hij hjr' i_fin hjr hhlt ih =>
    unfold loop; simp [-Fin.getElem_fin, *]
    have hi : i < n := by omega
    have hj : j < n := by omega
    rw [Nat.add_lt_add_iff_right] at ih
    let j_fin : Fin n := ⟨j, hj⟩

    constructor
    apply RangeHas.prepend (ha := hi) (pred := (¬lt _ _[·] = _))
    · let x : Partition α n := (loop left right hr pivot (arr.swap i_fin j_fin) (i + 1) (j + 1) (by omega) (by omega) (by omega)).val
      have hperm : PermStabilizing' _ _ x.arr' _ := partition.loop.permStabilizing
      simp only [hperm.2.1 i_fin (by simp only ; omega), Fin.getElem_fin, arr.getElem_swap_left]
      exact lt_asymm hhlt

    all_goals
      intro _ _ _
      try apply split_ih_left ih
      try apply split_ih_right ih
      any_goals simp only [i_fin]
      any_goals omega
      · intro hij'
        simp only [Vector.inclusive_swap hij']
        exact hxij hij'
      · simp only [Fin.getElem_fin, show (arr.swap ⟨i, by omega⟩ ⟨j, by omega⟩)[right] = _ by
          apply arr.getElem_swap_of_ne; all_goals simp; omega]
        exact hxr
      · simp only [Fin.getElem_fin, show (arr.swap ⟨i, by omega⟩ ⟨j, by omega⟩)[right] = _ by
          apply arr.getElem_swap_of_ne; all_goals simp; omega]
        exact hxr'

  | case2 arr i j hli hij hjr' hjr hhle ih =>
    unfold loop; simp [-Fin.getElem_fin, *]
    have hj : j < n := by omega

    constructor; all_goals
    intro _ _ _
    try apply split_ih_right ih
    try apply split_ih_left ih
    any_goals omega
    · intro _
      cases Nat.eq_or_lt_of_le hij with
      | inr hlt =>
        apply RangeHas.append hhle (hxij hlt) (hb := hj)
      | inl heq =>
        rw [heq]
        intro k _ _
        simpa only [Fin.getElem_fin, (by omega : k = j)]
    · exact hxr
    · exact hxr'

  | case3 arr i j hli hij _ _ =>
    unfold loop; simp [-Fin.getElem_fin, *]
    have hi : i < n := by omega

    constructor
    · simp only [Fin.getElem_fin]
      simpa only [RangeHas.singular (h := hi), arr.getElem_swap_left]
    ·
      have _ := show j = right by omega
      -- subst this
      subst right
      simp_all only [show i - 1 + 1 = i by omega]
      -- simp only [show right = j by omega, show i - 1 + 1 = i by omega] at *
      -- simp_all only [show right = j by omega, show i - 1 + 1 = i by omega]
      -- clear hr
      -- rw [show right = j by omega] at hr -- FIXME: @somombo <-- should not be necessary, simp_all line should be enough to replace all occurrences of right with j

      cases Nat.eq_or_lt_of_le hij with
      | inr hlt =>
        apply RangeHas.mono
        show RangeHas _ _ i (j + 1)
        apply RangeHas.prepend (ha := hi) (pred := (¬lt _[·] _ = _))
        · simpa only [Fin.getElem_fin, arr.getElem_swap_left]
        · simp only [Vector.inclusive_swap (hi := hi) (hj := hr) hlt]
          exact hxij hlt
        all_goals omega
      | inl heq =>
        simp only [Fin.getElem_fin]
        simpa only [heq, swap_self, RangeHas.singular (h := hr), ne_eq]


variable (le_trans : ∀ {x y z : α}, ¬lt y x → ¬lt z y → ¬lt z x)

include le_trans in
include lt_asymm in
protected theorem partition.sorted {arr : Vector α n} {left : Nat} {right : Nat} {hlr : left < right} {hr : right < n} : ∃ (pivot : α), Partitioned left right pivot (partition arr left right hlr hr).val := by
  let mid := left + ((right - left)/2)
  have hlm : left ≤ mid := Nat.le_add_right left ((right - left) / 2)
  have hlr_ :  left ≤ right := Nat.le_of_succ_le hlr
  have hmr :  mid ≤ right :=
    have : ((right - left)/2) ≤ right-left := Nat.div_le_self (right - left) 2
    have : left + ((right - left)/2) ≤ left + (right - left) := Nat.add_le_add_left this left
    Trans.trans this (Nat.add_sub_of_le hlr_)
  have hm :  mid < n := Trans.trans hmr hr

  let arr_ := arr |> (sortAt · left mid hlm hm) |> (sortAt · left right hlr_ hr) |> (sortAt · mid right hmr hr)
  let pivot := arr_[right]

  have hbase : ¬lt pivot arr_[left] ∧ ¬lt arr_[right] pivot :=
    have : ¬lt arr_[mid] arr_[left] ∧ ¬lt arr_[right] arr_[mid] := sortAt_of_sortAt_of_sortAt_sorted (lt_asymm := lt_asymm) (le_trans := le_trans) hlm hmr hr
    ⟨le_trans this.left this.right, lt_irrefl lt_asymm arr_[right]⟩

  let x : Partition α n := (partition.loop left right hr pivot arr_ (left + 1) (left + 1) (by omega) (by omega) (by omega)).val

  have hperm : PermStabilizing' (left + 1) right x.arr' arr_ := partition.loop.permStabilizing

  have hsort : RangeHas n (¬lt pivot x.arr'[·]) (left + 1) x.i' ∧ RangeHas n (¬lt x.arr'[·] pivot) (x.j' + 1) (right + 1) := by
    apply partition.loop.sorted lt_asymm
    · intro _ ; omega
    · exact hbase.right
    · exact hbase.right

  refine ⟨pivot, ?_⟩
  constructor
  · apply RangeHas.prepend (ha := by omega) (pred := (¬lt _ _[·] = _))
    · exact hperm.2.1 ⟨left, by omega⟩ (by simp only ; omega) |>.symm ▸ hbase.left
    · exact hsort.left
  ·  exact hsort.right


end lomuto


-- private class LT_Asymm (α : Type u) [Ord α] : Prop where
-- private class LE_Trans (α : Type u) [Ord α] : Prop where

-- -- variable (le_trans : ∀ {x y z : α}, ¬lt y x → ¬lt z y → ¬lt z x)
-- -- variable (lt_asymm : ∀ {x y : α}, lt x y → ¬lt y x)

class StrictOrder (α : Type u) [Ord α]  : Prop where
  lt_asymm : ∀ {x y : α}, lt x y → ¬lt y x
  le_trans : ∀ {x y z : α}, ¬lt y x → ¬lt z y → ¬lt z x

export StrictOrder (lt_asymm le_trans)


class LawfulPartitioningAlgorithm (part : PartitioningAlgorithm α) : Prop where
  partitionBounds : (part as left right hlr hr).val.j' < (part as left right hlr hr).val.i'
  permStabilizing : PermStabilizing' left right (part as left right hlr hr).val.arr' as
  sorting [StrictOrder α] (as : Vector α n) (hlr : left < right) (hr : right < n) : ∃ (pivot : α), Partitioned left right pivot (part as left right hlr hr).val

instance instLawfulHoarePartitioningAlgorithm : LawfulPartitioningAlgorithm (α := α) hoare.partition where
  partitionBounds := hoare.partition.partition_bounds
  permStabilizing := hoare.partition.permStabilizing
  sorting _ _ _ := hoare.partition.sorted lt_asymm le_trans

instance instLawfulLomutoPartitioningAlgorithm : LawfulPartitioningAlgorithm (α := α) lomuto.partition where
  partitionBounds := lomuto.partition.partition_bounds
  permStabilizing := lomuto.partition.permStabilizing
  sorting _ _ _ := lomuto.partition.sorted lt_asymm le_trans

instance instLawfulDefaultPartitioningAlgorithm : LawfulPartitioningAlgorithm (α := α) (@default _ _) := by
  simp only [default]; first
  | exact instLawfulHoarePartitioningAlgorithm
  | exact instLawfulLomutoPartitioningAlgorithm


----------------



theorem qs.strict.permStabilizing [LawfulPartitioningAlgorithm part] {as : Vector α n} {left right : Nat} {hsize' : right ≤ n - 1} : PermStabilizing' left right (qs.strict part as left right hsize') as := by
  induction as, left, right, hsize' using qs.strict.induct (part := part) with
  | case1 as left right hsize' hlr as' j' i' hli hjr heq as'' ih1 ih2 =>
    unfold qs.strict; simp [*]

    have ih0 := heq ▸ LawfulPartitioningAlgorithm.permStabilizing (part := part)
    replace ih1 : PermStabilizing' left right .. := ih1.mono (by omega) (by omega)
    replace ih2 : PermStabilizing' left right .. := ih2.mono (by omega) (by omega)

    exact ih2 |>.trans ih1 |>.trans ih0
  | case2 as left right hsize' hlr =>
    unfold qs.strict; simp [*]
    apply PermStabilizing'.refl

theorem qs.perm' [LawfulPartitioningAlgorithm part] {as : Array α} {left : Nat} {right : Nat}  : qs as left right part ~ as := by
  simp only [qs]; split
  any_goals simp only [panicWithPosWithDecl, panic, panicCore, *]
  all_goals exact qs.strict.permStabilizing.1

theorem qs.perm {as : Array α} : qs as ~ as := qs.perm'


@[simp]
theorem qs.qs_size [LawfulPartitioningAlgorithm part] {as : Array α}  :
    (qs as left right part).size = as.size := qs.perm'.length_eq


theorem qs.strict.monotinic [StrictOrder α] [LawfulPartitioningAlgorithm part] {as : Vector α n} {hsize' : right ≤ n - 1} : let q := (qs.strict part as left right hsize'); ∀ (i j : Fin n), (left ≤ i) → (i < j) → (j ≤ right) → ¬lt q[j] q[i] := by
  induction as, left, right, hsize' using qs.strict.induct (part := part) with
  | case1 as left right hsize' hlr as' j' i' hli' hjr' heq as'' ih1 ih2 =>
    unfold qs.strict; simp only [↓reduceDIte, hlr, heq]

    intro i j hli hij hjr; exact

    have hji' : j' < i' := by apply heq
      ▸ LawfulPartitioningAlgorithm.partitionBounds (part := part)
    let as''' := qs.strict part as'' i' right (by omega)

    if hhi : i' ≤ i then by
      apply ih2 <;> assumption
    else if hhj : j ≤ j' then by
      rw [qs.strict.permStabilizing.2.left j (by omega), qs.strict.permStabilizing.2.left i (by omega)]
      apply ih1 <;> assumption
    else by
      replace hhi : i < i' := by omega
      replace hhj : j' < j := by omega

      have ⟨pivot, ih0⟩ := LawfulPartitioningAlgorithm.sorting (part := part) as hlr (by omega)
      -- ih0 : Partitioned left right pivot (part as left right hlr hr).val

      replace ih0 :
          (∀ (i : Fin n), left ≤ i → i < i' → ¬lt pivot as'[i]) ∧
          (∀ (j : Fin n), j' + 1 ≤ j → j < right + 1 → ¬lt as'[j] pivot) := by
        unfold Partitioned at ih0; rwa [heq] at ih0

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

-- variable (lt_asymm : ∀ {x y : α}, (lt x y) → ¬lt y x)

theorem qs.monotinic' [StrictOrder α] {as : Array α} {left : Nat} {right : Nat} {part : PartitioningAlgorithm α} [LawfulPartitioningAlgorithm part] :  let q := (qs as left right part); ∀ (i j : Fin q.size), (left ≤ i) → (i < j) → (j ≤ right) → ¬lt q[j] q[i] := by
  simp only
  intro  i j _ _ _
  have _ : j.cast qs.qs_size ≤ as.size - 1 := by omega
  simp only [qs]; split
  any_goals simp only [panicWithPosWithDecl, panic, panicCore, *]
  all_goals apply qs.strict.monotinic (i.cast qs.qs_size) (j.cast qs.qs_size) <;> assumption


theorem qs.monotinic [StrictOrder α] {as : Array α} {part : PartitioningAlgorithm α} [LawfulPartitioningAlgorithm part]: ∀ (i j : Fin (qs (part := part) as).size), i < j → ¬lt (qs (part := part) as)[j] (qs (part := part) as)[i] := by
  intro i j h
  apply qs.monotinic'
  · omega
  · exact h
  · have := j.2; simp only [qs.qs_size] at this; omega


theorem qs.monotinic_with_defaults [StrictOrder α] {as : Array α} : ∀ (i j : Fin (qs as).size), i < j → ¬lt (qs as)[j] (qs as)[i] := qs.monotinic

example [StrictOrder α] {as : Array α} : let q := (qs (part := hoare.partition) as); ∀ (i j : Fin q.size), i < j → ¬lt q[j] q[i] := qs.monotinic
example [StrictOrder α] {as : Array α} : let q := (qs (part := lomuto.partition) as); ∀ (i j : Fin q.size), i < j → ¬lt q[j] q[i] := qs.monotinic

-- def unlawful_partition [Ord α] {n : Nat} (arr : Vector α n) (left : Nat)  (right : Nat) (hlr : left < right) (hr : right < n) : {x : Partition α n // (left < x.i') ∧ (x.j' < right)} := sorry

-- example {as : Array α} : let q := (qs (part := unlawful_partition) as); ∀ (i j : Fin q.size), i < j → ¬lt q[j] q[i] := qs.monotinic (part := unlawful_partition) -- <-- Should not work
