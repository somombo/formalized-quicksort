import Quicksort.Utils.RangeHas
import Quicksort.Utils.PermStabalizing
import Quicksort.Partition.Init.Basic
import Batteries.Data.Array.Lemmas
open Batteries Vector

variable [Ord α]

theorem maybeSwap_permStabilizing {as : Vector α n} {i j : Fin n} {left right : Nat} (h_i1 : left ≤ i) (h_i2 : i ≤ right) (h_j1 : left ≤ j) (h_j2 : j ≤ right) : PermStabilizing' left right (as.maybeSwap i j) as := by
  unfold maybeSwap
  split
  · apply swap_permStabilizing' <;> assumption
  · rfl

-- @[simp] theorem hoare.maybeSwap_swap_self (as : Vector α n) (i : Fin n ) : ∀ (x : Nat) (_ : x < n), (maybeSwap as i i)[x] =  as[x] := by unfold maybeSwap; split <;> simp


abbrev Partition.IsPartitioned (i j : Nat) (pivot : α) (x : Partition α n) :=
  RangeHas n (¬lt pivot  x.arr'[·]) i x.i' ∧ RangeHas n (¬lt x.arr'[·]  pivot) (x.j' + 1) (j + 1)

-- theorem Partition.IsPartitioned.of_IsPartitioned_of_permStabilizing {arr' : Vector α n} {i' j' : Nat} {x : Partition α n} (hpart : IsPartitioned i j pivot ⟨arr', j', i'⟩) (hperm : PermStabilizing' i' j' x.arr' arr')
-- : IsPartitioned i j pivot ⟨x.arr', j', i'⟩ := by
--   constructor; all_goals intro k h1 h2
--   · rw [hperm.2.1 k h2]
--     apply hpart.1 k h1 h2
--   · rw [hperm.2.2 k h1]
--     apply hpart.2 k h1 h2
