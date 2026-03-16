import Quicksort.Partition.Lemmas
import Quicksort.Basic

open Partition
open Array

variable (lt : α → α → Bool := by exact (· < ·))


theorem qs.strict.permStabilizing [LawfulScheme (lt := lt) @part] {as : Vector α n} {left right : Nat} {hsize' : right ≤ n - 1} : Vector.PermStabilizing' left right (qs.strict (lt := lt) @part as left right hsize') as := by
  induction as, left, right, hsize' using qs.strict.induct (lt := lt) (part := @part) with
  | case1 as left right hsize' hlr as' j' i' hli hjr heq as'' ih1 _ih1 ih2 =>
    unfold qs.strict; simp [*]

    have ih0 := heq ▸ LawfulScheme.permStabilizing (part := @part)
    replace ih1 : Vector.PermStabilizing' left right .. := ih1.mono (by omega) (by omega)
    replace ih2 : Vector.PermStabilizing' left right .. := ih2.mono (by omega) (by omega)

    exact ih2 |>.trans ih1 |>.trans ih0
  | case2 as left right hsize' hlr =>
    unfold qs.strict; simp [*]
    apply Vector.PermStabilizing'.refl

theorem qs.perm' [LawfulScheme (lt := lt) @part] {as : Array α} {left : Nat} {right : Nat}  : (qs (lt := lt) as left right @part).Perm as := by
  simp only [qs]; split
  any_goals simp only [panicWithPosWithDecl, panic, panicCore, *]
  all_goals
  have := qs.strict.permStabilizing  (lt := lt) (part := @part) (as := Vector.mk as rfl) (left := left) (hsize' := by solve_by_elim) |>.1
  grind [Vector.Perm]


theorem qs.perm {as : Array α} : (qs (lt := lt) as).Perm as := qs.perm' (lt := lt)


@[simp]
theorem qs.qs_size [LawfulScheme (lt := lt) @part] {as : Array α} :
    (qs (lt := lt) as left right @part).size = as.size := (qs.perm' (lt := lt)).size_eq


theorem qs.strict.monotonic [StrictOrder (lt := lt) α] [LawfulScheme (lt := lt) @part] {as : Vector α n} {hsize' : right ≤ n - 1} : let q := (qs.strict (lt := lt) @part as left right hsize'); ∀ (i j : Fin n), (left ≤ i) → (i < j) → (j ≤ right) → ¬lt q[j] q[i] := by
  induction as, left, right, hsize' using qs.strict.induct (lt := lt) (part := @part) with
  | case1 as left right hsize' hlr as' j' i' hli' hjr' heq as'' ih1 _ih1 ih2 =>
    unfold qs.strict; simp only [↓reduceDIte, hlr, heq]

    intro i j hli hij hjr; exact

    have hji' : j' < i' := by apply heq
      ▸ LawfulScheme.partitionBounds (part := @part)
    let as''' := qs.strict (lt := lt) @part as'' i' right (by omega)

    if hhi : i' ≤ i then by
      apply ih2 <;> assumption
    else if hhj : j ≤ j' then by
      rw [(qs.strict.permStabilizing (lt := lt)).2.left j (by omega), (qs.strict.permStabilizing (lt := lt)).2.left i (by omega)]
      apply ih1 <;> assumption
    else by
      replace hhi : i < i' := by omega
      replace hhj : j' < j := by omega

      have ⟨pivot, ih0⟩ := LawfulScheme.sorting  (lt := lt)  (part := @part) as hlr (by omega)
      -- ih0 : Partitioned left right pivot (part as left right hlr hr).val

      replace ih0 :
          (∀ (i : Fin n), left ≤ i → i < i' → ¬lt pivot as'[i]) ∧
          (∀ (j : Fin n), j' + 1 ≤ j → j < right + 1 → ¬lt as'[j] pivot) := by
        unfold Partition.IsPartitioned at ih0; rwa [heq] at ih0

      have hhh1 : ¬lt pivot as'''[i] :=
        suffices ¬lt pivot as''[i] by rwa [(qs.strict.permStabilizing (lt := lt)).2.left i (by omega)]
        if _ : i ≤ j' then by
          apply Vector.PermStabilizing'.invariance (motive := (¬lt pivot ·)) (left := left) (hi := j' + 1) (hperm := (qs.strict.permStabilizing (lt := lt))) (h := ?_ )
          any_goals omega
          · intro i_ _ _
            apply ih0.left i_ <;> omega
        else by
          rw [(qs.strict.permStabilizing (lt := lt)).2.right _ ?_]
          apply ih0.left i
          all_goals omega

      have hhh2 : ¬lt as'''[j] pivot :=
        if _ : i' ≤ j then by
          apply Vector.PermStabilizing'.invariance (motive := (¬lt · pivot)) (left := i') (hi := right + 1) (hperm := (qs.strict.permStabilizing (lt := lt))) (h := ?_)
          any_goals omega
          · intro j_ _ _
            rw [(qs.strict.permStabilizing (lt := lt)).2.right j_ (by omega)]
            apply ih0.right j_ <;> omega
        else by
          rw [(qs.strict.permStabilizing (lt := lt)).2.left _ ?_, (qs.strict.permStabilizing (lt := lt)).2.right _ ?_]
          apply ih0.right j
          all_goals omega
      exact le_trans hhh1 hhh2
  | case2 => omega

-- variable (lt_asymm : ∀ {x y : α}, (lt x y) → ¬lt y x)

theorem qs.monotonic' [StrictOrder (lt := lt) α] {as : Array α} {left : Nat} {right : Nat} {part : Partition.Scheme α} [LawfulScheme (lt := lt) @part] :  let q := (qs (lt := lt) as left right @part); ∀ (i j : Fin q.size), (left ≤ i) → (i < j) → (j ≤ right) → ¬lt q[j] q[i] := by
  simp only
  intro  i j _ _ _
  have _ : j.cast (qs.qs_size (lt := lt)) ≤ as.size - 1 := by omega
  simp only [qs]; split
  any_goals simp only [panicWithPosWithDecl, panic, panicCore, *]
  all_goals apply qs.strict.monotonic (lt := lt) (i.cast (qs.qs_size (lt := lt))) (j.cast (qs.qs_size (lt := lt))) <;> assumption

theorem qs.monotonic [StrictOrder (lt := lt) α] {as : Array α} {part : Partition.Scheme α} [LawfulScheme (lt := lt) @part]: ∀ (i j : Fin (qs (lt := lt) (part := @part) as).size), i < j → ¬lt (qs (lt := lt) (part := @part) as)[j] (qs (lt := lt) (part := @part) as)[i] := by
  intro i j h
  apply qs.monotonic'
  · omega
  · exact h
  · have := j.2; simp only [qs.qs_size] at this; omega


theorem qs.monotonic_with_defaults [StrictOrder (lt := lt) α] {as : Array α} : ∀ (i j : Fin (qs (lt := lt) as).size), i < j → ¬lt (qs (lt := lt) as)[j] (qs (lt := lt) as)[i] := qs.monotonic (lt := lt)

example [StrictOrder (lt := lt) α] {as : Array α} : let q := (qs (lt := lt) (part := @Partition.hoare α) as); ∀ (i j : Fin q.size), i < j → ¬lt q[j] q[i] := qs.monotonic (lt := lt)
example [StrictOrder (lt := lt) α] {as : Array α} : let q := (qs (lt := lt) (part := @Partition.lomuto α) as); ∀ (i j : Fin q.size), i < j → ¬lt q[j] q[i] := qs.monotonic (lt := lt)

-- def unlawful_partition (lt : α → α → Bool := by exact (· < ·)) {n : Nat} (arr : Vector α n) (left : Nat)  (right : Nat) (hlr : left < right) (hr : right < n) : {x : Partition α n // (left < x.i') ∧ (x.j' < right)} := sorry

-- example {as : Array α} : let q := (qs (part := unlawful_partition) as); ∀ (i j : Fin q.size), i < j → ¬lt q[j] q[i] := qs.monotonic (part := unlawful_partition) -- <-- Should not work
