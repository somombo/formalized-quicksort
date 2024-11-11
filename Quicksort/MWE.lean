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



-- theorem sortAt_permStabilizing (as : Vector α n) (low high : Nat) (hlh : low ≤ high) (hn : high < n) :  PermStabilizing' low high (sortAt as low high hlh hn) as  := sorry

theorem sortAt_of_sortAt_of_sortAt_permStabilizing {arr : Vector α n} {left mid right: Nat} (hlm : left ≤ mid) (hmr : mid ≤ right) (hr : right < n) :
  arr
    |> (sortAt · left mid hlm (by omega))
    |> (sortAt · left right (by omega) hr)
    |> (sortAt · mid right hmr hr)
    |> (PermStabilizing' left right · arr)
  := sorry


-- include lt_asymm in
-- theorem sortAt_sorted (as : Vector α n) (low high : Nat) (hlh : low ≤ high) (hn : high < n) : ¬ (lt (sortAt as low high hlh hn)[high] (sortAt as low high hlh hn)[low]) := sorry

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
  := sorry

abbrev Partitioned (i j : Nat) (pivot : α) (x : Partition α n) :=
  RangeHas n (¬lt pivot  x.arr'[·]) i x.i' ∧ RangeHas n (¬lt x.arr'[·]  pivot) (x.j' + 1) (j + 1)

end init

namespace hoare


protected theorem partition.partition_bounds {arr : Vector α n} {left : Nat} {right : Nat} {hlr : left < right} {hr : right < n} : (partition arr left right hlr hr).val.j' < (partition arr left right hlr hr).val.i' := sorry


protected theorem partition.permStabilizing {arr : Vector α n} {left : Nat} {right : Nat} {hlr : left < right} {hr : right < n} : PermStabilizing' left right (partition arr left right hlr hr).val.arr' arr := sorry


variable (lt_asymm : ∀ {x y : α}, lt x y → ¬lt y x)
variable (le_trans : ∀ {x y z : α}, ¬lt y x → ¬lt z y → ¬lt z x)

include le_trans in
include lt_asymm in
protected theorem partition.sorted {arr : Vector α n} {left : Nat} {right : Nat} {hlr : left < right} {hr : right < n} : ∃ (pivot : α), Partitioned left right pivot (partition arr left right hlr hr).val := sorry

end hoare




namespace lomuto



protected theorem partition.partition_bounds {arr : Vector α n} {left : Nat} {right : Nat} {hlr : left < right} {hr : right < n} : (partition arr left right hlr hr).val.j' < (partition arr left right hlr hr).val.i' := sorry


protected theorem partition.permStabilizing {arr : Vector α n} {left : Nat} {right : Nat} {hlr : left < right} {hr : right < n} : PermStabilizing' left right (partition arr left right hlr hr).val.arr' arr := sorry


variable (lt_asymm : ∀ {x y : α}, lt x y → ¬lt y x)
variable (le_trans : ∀ {x y z : α}, ¬lt y x → ¬lt z y → ¬lt z x)

include le_trans in
include lt_asymm in
protected theorem partition.sorted {arr : Vector α n} {left : Nat} {right : Nat} {hlr : left < right} {hr : right < n} : ∃ (pivot : α), Partitioned left right pivot (partition arr left right hlr hr).val := sorry


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
