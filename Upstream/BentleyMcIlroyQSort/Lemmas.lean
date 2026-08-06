import Quicksort.Init.RangeHas
import Quicksort.Init.PermStabalizing

import Upstream.BentleyMcIlroyQSort.Basic

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


end Partition







open Vector


section qsort_bentleyMcIlroy

open Partition
open Array

variable [Ord α]

open Ord

theorem qsort_bentleyMcIlroy.sort.permStabilizing {as : Vector α n} {left right : Nat} {hsize' : right ≤ n - 1} : Vector.PermStabilizing' left right (sort as left right hsize') as := by
  sorry

theorem qsort_bentleyMcIlroy.perm' {as : Array α} {left : Nat} {right : Nat}  : (qsort_bentleyMcIlroy as left right).Perm as := by
  simp only [qsort_bentleyMcIlroy]; split
  any_goals simp only [panicWithPosWithDecl, panic, panicCore, *]
  all_goals
  have := qsort_bentleyMcIlroy.sort.permStabilizing (as := Vector.mk as rfl) (left := left) (hsize' := by solve_by_elim) |>.1
  grind [Vector.Perm]


theorem qsort_bentleyMcIlroy.perm {as : Array α} : (qsort_bentleyMcIlroy as).Perm as := qsort_bentleyMcIlroy.perm'


@[simp]
theorem qsort_bentleyMcIlroy.qs_size {as : Array α} :
    (qsort_bentleyMcIlroy as left right).size = as.size := qsort_bentleyMcIlroy.perm'.size_eq

variable [Std.TransOrd α]
theorem qsort_bentleyMcIlroy.sort.monotonic {as : Vector α n} {hsize' : right ≤ n - 1} : let q := (sort as left right hsize'); ∀ (i j : Fin n), (left ≤ i) → (i < j) → (j ≤ right) → ¬lt q[j] q[i] := by
  sorry

theorem qsort_bentleyMcIlroy.monotonic' {as : Array α} {left : Nat} {right : Nat} :  let q := (qsort_bentleyMcIlroy as left right); ∀ (i j : Fin q.size), (left ≤ i) → (i < j) → (j ≤ right) → ¬lt q[j] q[i] := by
  simp only
  intro  i j _ _ _
  have _ : j.cast qsort_bentleyMcIlroy.qs_size ≤ as.size - 1 := by omega
  simp only [qsort_bentleyMcIlroy]; split
  any_goals simp only [panicWithPosWithDecl, panic, panicCore, *]
  all_goals apply qsort_bentleyMcIlroy.sort.monotonic (i.cast qsort_bentleyMcIlroy.qs_size) (j.cast qsort_bentleyMcIlroy.qs_size) <;> assumption

theorem qsort_bentleyMcIlroy.monotonic {as : Array α} : ∀ (i j : Fin (qsort_bentleyMcIlroy as).size), i < j → ¬lt (qsort_bentleyMcIlroy as)[j] (qsort_bentleyMcIlroy as)[i] := by
  intro i j h
  apply qsort_bentleyMcIlroy.monotonic'
  · omega
  · exact h
  · have := j.2; simp only [qsort_bentleyMcIlroy.qs_size] at this; omega



end qsort_bentleyMcIlroy

section qsort_bentleyMcIlroy_strict

open Partition
open Array

variable [Ord α]
variable [Std.TransOrd α]
open Ord

theorem qsort_bentleyMcIlroy_strict.sort.permStabilizing {as : Vector α n} {left right : Nat} {hsize' : right ≤ n - 1} : Vector.PermStabilizing' left right (sort as left right hsize') as := by
  sorry

theorem qsort_bentleyMcIlroy_strict.perm' {as : Array α} {left : Nat} {right : Nat}  : (qsort_bentleyMcIlroy_strict as left right).Perm as := by
  simp only [qsort_bentleyMcIlroy_strict]; split
  any_goals simp only [panicWithPosWithDecl, panic, panicCore, *]
  all_goals
  have := qsort_bentleyMcIlroy_strict.sort.permStabilizing (as := Vector.mk as rfl) (left := left) (hsize' := by solve_by_elim) |>.1
  grind [Vector.Perm]


theorem qsort_bentleyMcIlroy_strict.perm {as : Array α} : (qsort_bentleyMcIlroy_strict as).Perm as := qsort_bentleyMcIlroy_strict.perm'


@[simp]
theorem qsort_bentleyMcIlroy_strict.qs_size {as : Array α} :
    (qsort_bentleyMcIlroy_strict as left right).size = as.size := qsort_bentleyMcIlroy_strict.perm'.size_eq

theorem qsort_bentleyMcIlroy_strict.sort.monotonic {as : Vector α n} {hsize' : right ≤ n - 1} : let q := (sort as left right hsize'); ∀ (i j : Fin n), (left ≤ i) → (i < j) → (j ≤ right) → ¬lt q[j] q[i] := by
  sorry

theorem qsort_bentleyMcIlroy_strict.monotonic' {as : Array α} {left : Nat} {right : Nat} :  let q := (qsort_bentleyMcIlroy_strict as left right); ∀ (i j : Fin q.size), (left ≤ i) → (i < j) → (j ≤ right) → ¬lt q[j] q[i] := by
  simp only
  intro  i j _ _ _
  have _ : j.cast qsort_bentleyMcIlroy_strict.qs_size ≤ as.size - 1 := by omega
  simp only [qsort_bentleyMcIlroy_strict]; split
  any_goals simp only [panicWithPosWithDecl, panic, panicCore, *]
  all_goals apply qsort_bentleyMcIlroy_strict.sort.monotonic (i.cast qsort_bentleyMcIlroy_strict.qs_size) (j.cast qsort_bentleyMcIlroy_strict.qs_size) <;> assumption

theorem qsort_bentleyMcIlroy_strict.monotonic {as : Array α} : ∀ (i j : Fin (qsort_bentleyMcIlroy_strict as).size), i < j → ¬lt (qsort_bentleyMcIlroy_strict as)[j] (qsort_bentleyMcIlroy_strict as)[i] := by
  intro i j h
  apply qsort_bentleyMcIlroy_strict.monotonic'
  · omega
  · exact h
  · have := j.2; simp only [qsort_bentleyMcIlroy_strict.qs_size] at this; omega



end qsort_bentleyMcIlroy_strict
