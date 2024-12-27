
import Quicksort.Partition.Hoare.Basic
import Quicksort.Partition.Hoare.Eager.Lemmas
import Quicksort.Partition.Hoare.Classic.Lemmas
import Quicksort.Partition.Init.Lemmas

open Batteries Vector

namespace Partition
variable [Ord α]
variable (lt_asymm : ∀ {x y : α}, lt x y → ¬lt y x)

-- include lt_asymm in
-- private theorem lt_irrefl : ∀ (x : α), ¬lt x x :=
--   fun _ h => (lt_asymm h) h


variable (le_trans : ∀ {x y z : α}, ¬lt y x → ¬lt z y → ¬lt z x)




-- include lt_asymm in
-- private theorem hoare.maybeSwap_sorted (as : Vector α n) (low high : Nat) (hlh : low ≤ high) (hn : high < n) : ¬lt (maybeSwap as ⟨low, by omega⟩ ⟨high, by omega⟩)[high] (maybeSwap as ⟨low, by omega⟩ ⟨high, by omega⟩)[low] := by
--   unfold maybeSwap; split
--   · next h =>
--       have _ := lt_asymm h
--       simp_all [as.getElem_swap_right, as.getElem_swap_left]
--   · assumption



-- -- set_option trace.profiler true in
-- include lt_asymm in
-- include le_trans in
-- private theorem hoare.median_of_three_sorted {arr : Vector α n} {left mid right: Nat} (hlm : left ≤ mid) (hmr : mid ≤ right) (hr : right < n) :
--   let_fun arr_ := arr
--     |> (maybeSwap · ⟨left, by omega⟩ ⟨mid, by omega⟩)
--     |> (maybeSwap · ⟨left, by omega⟩ ⟨right, by omega⟩)
--     |> (maybeSwap · ⟨mid, by omega⟩ ⟨right, by omega⟩)
-- -- ∀ {k_ : Nat} (_ : left ≤ k_) (_ : k_ ≤ right),
--   ¬lt arr_[mid] arr_[left] ∧ ¬lt arr_[right] arr_[mid]
--   :=
--   have _ : left < n := by omega
--   have _ : mid < n := by omega

--   let arr1 : Vector α n := maybeSwap arr ⟨left, by omega⟩ ⟨mid, by omega⟩
--   let arr2 : Vector α n := maybeSwap arr1 ⟨left, by omega⟩ ⟨right, by omega⟩
--   let arr_ : Vector α n := maybeSwap arr2 ⟨mid, by omega⟩ ⟨right, by omega⟩

--   have hh1 : ¬lt arr1[mid] arr1[left] := maybeSwap_sorted lt_asymm arr left mid (by omega) (by omega)
--   have hh2 : ¬lt arr2[right] arr2[left] := maybeSwap_sorted lt_asymm arr1 left right (by omega) (by omega)
--   have hh_ : ¬lt arr_[right] arr_[mid] := maybeSwap_sorted lt_asymm arr2 mid right (by omega) (by omega)

--   suffices ¬lt arr_[mid] arr_[left] from ⟨this, hh_⟩

--   if hleqm : left = mid then by
--     simp only [hleqm]
--     exact lt_irrefl lt_asymm arr_[mid]
--   else by
--     have hlneqr : left ≠ right := by omega
--     simp only [arr_]
--     unfold maybeSwap
--     split
--     · have : (arr2.swap ⟨mid, ‹_›⟩ ⟨right, ‹_›⟩)[left] = _ :=
--         arr2.getElem_swap_of_ne _ hleqm hlneqr
--       simp only [this, arr2.getElem_swap_left, Fin.getElem_fin]
--       assumption
--     · exact
--       if hmeqr : mid = right then by
--         simp only [hmeqr]
--         exact hh2
--       else by
--         simp only [arr2]
--         unfold maybeSwap
--         split
--         · have : (arr1.swap ⟨left, by omega⟩ ⟨right, hr⟩)[mid] = _ :=
--             arr1.getElem_swap_of_ne (_ : mid < n) (Ne.symm hleqm) hmeqr
--           simp only [this, arr1.getElem_swap_left, Fin.getElem_fin]
--           refine le_trans (lt_asymm ?_) hh1
--           assumption
--         · assumption



protected theorem hoare.partition_bounds {arr : Vector α n} {left : Nat} {right : Nat} {hlr : left < right} {hr : right < n} : (Partition.hoare arr left right hlr hr).val.j' < (Partition.hoare arr left right hlr hr).val.i' := by
  unfold Partition.hoare; simp [*]; split
  · apply hoare.classic.loop.partition_bounds
  · apply hoare.eager.partition_bounds; assumption




protected theorem hoare.permStabilizing {arr : Vector α n} {left : Nat} {right : Nat} {hlr : left < right} {hr : right < n} : PermStabilizing' left right (Partition.hoare arr left right hlr hr).val.arr' arr := by
  unfold Partition.hoare; simp [*]; split
  · apply PermStabilizing'.trans
    · apply PermStabilizing'.mono hoare.classic.loop.permStabilizing <;> simp_arith
    · apply PermStabilizing'.trans
      apply PermStabilizing'.trans
      all_goals apply maybeSwap_permStabilizing
      all_goals simp only; omega
  · apply hoare.eager.permStabilizing; assumption

-- private abbrev Partition.IsPartitioned (i j : Nat) (pivot : α) (x : Partition α n) := RangeHas n (¬lt pivot  x.arr'[·]) i x.i' ∧ RangeHas n (¬lt x.arr'[·]  pivot) (x.j' + 1) (j + 1)

-- variable (lt_asymm : ∀ {x y : α}, lt x y → ¬lt y x)
-- variable (le_trans : ∀ {x y z : α}, ¬lt y x → ¬lt z y → ¬lt z x)

include le_trans in
include lt_asymm in
protected theorem hoare.sorted {arr : Vector α n} {left : Nat} {right : Nat} {hlr : left < right} {hr : right < n} : ∃ (pivot : α), IsPartitioned left right pivot (Partition.hoare arr left right hlr hr).val := by
  unfold Partition.hoare; simp [*]; split
  · apply hoare.classic.sorted <;> assumption
  · apply hoare.eager.sorted <;> assumption

  -- let mid := left + ((right - left)/2)
  -- have hlm : left ≤ mid := Nat.le_add_right left ((right - left) / 2)
  -- have hlr_ :  left ≤ right := Nat.le_of_succ_le hlr
  -- have hmr :  mid ≤ right :=
  --   have : ((right - left)/2) ≤ right-left := Nat.div_le_self (right - left) 2
  --   have : left + ((right - left)/2) ≤ left + (right - left) := Nat.add_le_add_left this left
  --   Trans.trans this (Nat.add_sub_of_le hlr_)
  -- have hm :  mid < n := Trans.trans hmr hr

  -- let arr_ := arr
  --   |> (maybeSwap · ⟨left, by omega⟩ ⟨mid, by omega⟩)
  --   |> (maybeSwap · ⟨left, by omega⟩ ⟨right, by omega⟩)
  --   |> (maybeSwap · ⟨mid, by omega⟩ ⟨right, by omega⟩)
  -- let pivot := arr_[mid]

  -- let x : Partition α n := (loop left right hr pivot  arr_ (left + 1) (right - 1) (by omega) (by omega) (by omega)).val
  -- have : IsPartitioned left right pivot x := by
  --   have hh1 : IsPartitioned (left + 1) (right - 1) pivot x := hoare.loop.sorted (lt_asymm := lt_asymm)

  --   have hh2 : ¬lt pivot arr_[left] ∧ ¬lt arr_[right] pivot := hoare.median_of_three_sorted (lt_asymm := lt_asymm) (le_trans := le_trans) hlm hmr hr

  --   have : PermStabilizing' (left + 1) (right - 1) x.arr' arr_ := hoare.loop.permStabilizing
  --   replace hh2 : ¬lt pivot x.arr'[left] ∧ ¬lt x.arr'[right] pivot := by
  --     have heq_left : x.arr'[left] = arr_[left] := this.2.1 ⟨left, by omega⟩ (by simp_arith)
  --     have heq_right : x.arr'[right] = arr_[right] := this.2.2 ⟨right, by omega⟩ (by simp_arith; omega)
  --     rwa [heq_left, heq_right]

  --   have hh1_right : RangeHas n (¬lt x.arr'[·]  pivot) (x.j' + 1) right := by
  --     have : right - 1 + 1 = right := by omega
  --     rw [←this]; exact hh1.right
  --   exact ⟨RangeHas.prepend (ha := by omega) hh2.left hh1.left , RangeHas.append (hb := by omega) hh2.right hh1_right⟩
  -- ⟨pivot, this⟩
