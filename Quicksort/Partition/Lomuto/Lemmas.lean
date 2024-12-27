import Quicksort.Partition.Lomuto.Basic
import Quicksort.Partition.Init.Lemmas

open Batteries Vector

namespace Partition
variable [Ord α]
variable (lt_asymm : ∀ {x y : α}, lt x y → ¬lt y x)

include lt_asymm in
private theorem lt_irrefl : ∀ (x : α), ¬lt x x :=
  fun _ h => (lt_asymm h) h

protected theorem lomuto.loop.partition_bounds {left right : Nat}  {hlr : left < right} {hr : right < n} {pivot : α} {arr : Vector α n} {i j : Nat} {hli : left ≤ i} {hij : i ≤ j} {hjr : j ≤ right} : (loop left right hlr hr pivot arr i j hli hij hjr).val.j' < (loop left right hlr hr pivot arr i j hli hij hjr).val.i' := by
  induction arr, i, j, hli, hij, hjr using lomuto.loop.induct (hlr := hlr) (hr := hr) (pivot := pivot)  with
  | case1 arr i j hli hij hjr' i_fin hjr hhlt ih  =>
    unfold loop; simp [*]
  | case2 arr i j hli hij hjr' hjr hhle ih =>
    unfold loop; simp [*]
  | case3 arr i j hli hij hjr' hjr =>
    unfold loop; simp [*]
    omega

protected theorem lomuto.partition_bounds {arr : Vector α n} {left : Nat} {right : Nat} {hlr : left < right} {hr : right < n} : (lomuto arr left right hlr hr).val.j' < (lomuto arr left right hlr hr).val.i' := by
  unfold lomuto
  apply lomuto.loop.partition_bounds

protected theorem lomuto.loop.permStabilizing {left right : Nat} {hlr : left < right} {hr : right < n} {pivot : α} {arr : Vector α n} {i j : Nat} {hli : left ≤ i} {hij :  i ≤ j} {hjr : j ≤ right} : PermStabilizing' i right (loop left right hlr hr pivot arr i j hli hij hjr).val.arr' arr
:= by
  induction arr, i, j, hli, hij, hjr using lomuto.loop.induct (hlr := hlr) (hr := hr) (pivot := pivot) with
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

-- set_option trace.profiler true in
protected theorem lomuto.permStabilizing {arr : Vector α n} {left : Nat} {right : Nat} {hlr : left < right} {hr : right < n} : PermStabilizing' left right (lomuto arr left right hlr hr).val.arr' arr := by
  apply PermStabilizing'.trans
  · apply PermStabilizing'.mono lomuto.loop.permStabilizing <;> omega
  · -- apply sortAt_of_sortAt_of_sortAt_permStabilizing <;>  omega
    apply PermStabilizing'.trans
    apply PermStabilizing'.trans
    all_goals apply maybeSwap_permStabilizing
    all_goals simp only; omega


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
-- protected theorem lomuto.loop.sorted {left right : Nat} {hr : right < n} {pivot : α} {arr : Vector α n} {i j : Nat} {hli : left ≤ i} {hij :  i ≤ j} {hjr : j ≤ right} (hxij : i < j → RangeHas n (¬lt arr[·] pivot) i j ) (hxr : ¬lt arr[right] pivot) (hxr' : ¬lt pivot arr[right]) : let x := (loop left right hr pivot arr i j hli hij hjr).val; RangeHas n (¬lt pivot x.arr'[·]) i x.i' ∧  RangeHas n (¬lt x.arr'[·] pivot) (x.j' + 1) (right + 1) := by
protected theorem lomuto.loop.sorted {left right : Nat} {hlr : left < right} {hr : right < n} {pivot : α} {arr : Vector α n} {i j : Nat} {hli : left ≤ i} {hij :  i ≤ j} {hjr : j ≤ right} (hxij : i < j → RangeHas n (¬lt arr[·] pivot) i j ) (hxr : ¬lt arr[right] pivot) (hxr' : ¬lt pivot arr[right]) : IsPartitioned i right pivot (loop left right hlr hr pivot arr i j hli hij hjr).val := by

  induction arr, i, j, hli, hij, hjr using lomuto.loop.induct (hlr := hlr) (hr := hr) (pivot := pivot) with
  | case1 arr i j hli hij hjr' i_fin hjr hhlt ih =>
    unfold loop; simp [-Fin.getElem_fin, *]
    have hi : i < n := by omega
    have hj : j < n := by omega
    rw [Nat.add_lt_add_iff_right] at ih
    let j_fin : Fin n := ⟨j, hj⟩

    constructor
    apply RangeHas.prepend (ha := hi) (pred := (¬lt _ _[·] = _))
    · let x : Partition α n := (loop left right hlr hr pivot (arr.swap i_fin j_fin) (i + 1) (j + 1) (by omega) (by omega) (by omega)).val
      have hperm : PermStabilizing' _ _ x.arr' _ := lomuto.loop.permStabilizing
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
    · have hrj : j = right := by omega
      subst hrj
      suffices RangeHas n (¬lt (arr.swap ⟨i, hi⟩ ⟨j, hr⟩)[·] pivot) i (j + 1) by
        change RangeHas n (¬lt (arr.swap ⟨i, hi⟩ ⟨j, hr⟩)[·] pivot) (i - 1 + 1) (j + 1)
        apply RangeHas.mono this <;> omega

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

include lt_asymm in
protected theorem lomuto.sorted {arr : Vector α n} {left : Nat} {right : Nat} {hlr : left < right} {hr : right < n} : ∃ (pivot : α), IsPartitioned left right pivot (lomuto arr left right hlr hr).val := by
  let mid := left + ((right - left)/2)
  let arr_ := arr
    |> (maybeSwap · ⟨left, by omega⟩ ⟨mid, by omega⟩)
    |> (maybeSwap · ⟨left, by omega⟩ ⟨right, by omega⟩)
    |> (maybeSwap · ⟨right, by omega⟩ ⟨mid, by omega⟩)

  refine ⟨arr_[right], ?_⟩
  unfold lomuto

  apply lomuto.loop.sorted lt_asymm (by intro _ ; omega)
  all_goals apply lt_irrefl lt_asymm arr_[right]
