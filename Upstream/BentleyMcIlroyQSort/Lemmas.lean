import Upstream.Init.RangeHas
import Upstream.Init.PermStabalizing

import Upstream.BentleyMcIlroyQSort.Basic
import Upstream.BentleyMcIlroyQSort.Lemmas_perm

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


open Partition.bentleyMcIlroy.move_pivots_back

theorem move_p_back_bounds {α : Type u} [Ord α] {n : Nat} {right p : Nat} {hr : right < n} {hp : p < n} {k : Nat} {arr : Vector α n} {j : Nat} {hjr : j < right} {arr' : Vector α n} {j' : Nat} {hj' : j' < right} (h : move_p_back hr hp k arr j hjr = (arr', ⟨j', hj'⟩)) : j' ≤ j := by
  induction k, arr, j, hjr using move_p_back.induct hr hp
  case case1 ih =>
    unfold move_p_back at h
    simp [*] at h
    have := ih h
    omega
  case case2 =>
    unfold move_p_back at h
    simp [*] at h
    rcases h with ⟨_, rfl⟩
    omega

theorem move_q_forward_bounds {α : Type u} [Ord α] {n : Nat} {right q : Nat} {left : Nat} {hr : right < n} {i_0 : Nat} {hi'q : i_0 ≤ q + 1} {k : Nat} {arr : Vector α n} {i : Nat} {hkq : q + 1 ≤ k} {hil : left < i} {hieqk : i = k - (q + 1) + i_0} {arr' : Vector α n} {i'' : Nat} {hi'' : left < i''} (h : move_q_forward hr hi'q k arr i hkq hil hieqk = (arr', ⟨i'', hi''⟩)) : i ≤ i'' := by
  induction k, arr, i, hkq, hil, hieqk using move_q_forward.induct hr hi'q
  case case1 ih =>
    unfold move_q_forward at h
    simp [*] at h
    have := ih h
    omega
  case case2 =>
    unfold move_q_forward at h
    simp [*] at h
    rcases h with ⟨_, rfl⟩
    omega

theorem Partition.bentleyMcIlroy.eager.loop.partition_bounds [Ord α] {left right : Nat} {hlr : left < right} {hr : right < n} {pivot : α} {arr : Vector α n} {i j p q : Nat} {hpi : p ≤ i} {hqr : q < right} {hli : left < i} {hij : i ≤ j + 1} {hjr : j < right} {hjq : j ≤ q} :
    (eager.loop left right hlr hr pivot arr i j p q hli hij hjr hpi hqr hjq).val.j' < (eager.loop left right hlr hr pivot arr i j p q hli hij hjr hpi hqr hjq).val.i' := by
  induction arr, i, j, p, q, hli, hij, hjr, hpi, hqr, hjq using eager.loop.induct left right hlr hr pivot
  case case1 v_arr v_i v_j v_p v_q hli hij hjr hpi hqr hjq hp h arr'' j'' hi''r x1 arr''' i'' hli'' x2 =>
    rw [eager.loop]
    simp only []
    repeat (split <;> try contradiction)
    simp only [*]
    have hj''_le := move_p_back_bounds x1
    have hi''_le := move_q_forward_bounds x2
    omega
  case case2 v_arr v_i v_j v_p v_q hli hij hjr hpi hqr hjq hp h1 h ih =>
    rw [eager.loop]
    simp only []
    repeat (split <;> try contradiction)
    exact ih
  case case3 v_arr v_i v_j v_p v_q hli hij hjr hpi hqr hjq hp h2 h1 h ih =>
    rw [eager.loop]
    simp only []
    repeat (split <;> try contradiction)
    exact ih
  case case4 v_arr v_i v_j v_p v_q hli hij hjr hpi hqr hjq hp h5 h4 h3 h2 arr' h1 h ih =>
    rw [eager.loop]
    simp only []
    repeat (split <;> try contradiction)
    simp only [arr', Vector.getElem_swap_right, Vector.getElem_swap_left] at h1 h ih
    exact ih
  case case5 v_arr v_i v_j v_p v_q hli hij hjr hpi hqr hjq hp h5 h4 h3 h2 arr' h1 h arr'' ih =>
    rw [eager.loop]
    simp only []
    repeat (split <;> try contradiction)
    simp only [arr', arr'', Vector.getElem_swap_right, Vector.getElem_swap_left] at h1 h ih
    exact ih
  case case6 v_arr v_i v_j v_p v_q hli hij hjr hpi hqr hjq hp h5 h4 h3 h2 arr' h1 arr'' h ih =>
    rw [eager.loop]
    simp only []
    repeat (split <;> try contradiction)
    have hpj : v_j ≠ v_p := by omega
    have hpji : v_j ≠ v_i := by omega
    simp only [arr', arr'', Vector.getElem_swap_right, Vector.getElem_swap_left, Vector.getElem_swap_of_ne hpj hpji] at h1 h ih
    exact ih
  case case7 v_arr v_i v_j v_p v_q hli hij hjr hpi hqr hjq hp h5 h4 h3 h2 arr' h1 arr'' h arr''' ih =>
    rw [eager.loop]
    simp only []
    repeat (split <;> try contradiction)
    have hpj : v_j ≠ v_p := by omega
    have hpji : v_j ≠ v_i := by omega
    simp only [arr', arr'', arr''', Vector.getElem_swap_right, Vector.getElem_swap_left, Vector.getElem_swap_of_ne hpj hpji] at h1 h ih
    exact ih
  case case8 v_arr v_i v_j v_p v_q hli hij hjr hpi hqr hjq hp h3 h2 h1 h arr'' j'' hi''r x1 arr''' i'' hli'' x2 =>
    rw [eager.loop]
    simp only []
    repeat (split <;> try contradiction)
    simp only [*]
    have hj''_le := move_p_back_bounds x1
    have hi''_le := move_q_forward_bounds x2
    omega

theorem Partition.bentleyMcIlroy.classic.loop.partition_bounds [Ord α] [Std.TransOrd α] {left right : Nat} {hr : right < n} {hl : left < n} {pivot : α} {arr : Vector α n} {i j p q : Nat} {hpi : p ≤ i} {hqr : q < right} {hli : left < i} {hij : i ≤ j + 1} {hjr : j < right} {hjq : j ≤ q} {halgep : ¬lt pivot arr[p - 1]} {haqltp : ¬lt arr[q + 1] pivot} :
    (classic.loop left right hr hl pivot arr i j p q hpi hqr hli hij hjr hjq halgep haqltp).val.j' < (classic.loop left right hr hl pivot arr i j p q hpi hqr hli hij hjr hjq halgep haqltp).val.i' := by
  induction arr, i, j, p, q, hpi, hqr, hli, hij, hjr, hjq, halgep, haqltp using classic.loop.induct left right hr hl pivot
  case case1 v_arr v_i v_j v_p v_q hpi hqr hli hij hjr hjq halgep haqltp j' isLtj' left2 hjpiv1 x1 hjpiv i' isLti' left1 left_ hapiv1 x2 hapiv h_iltj hqsimp hpsimp arr_1 h1 h2 ih =>
    unfold classic.loop
    simp [arr_1, Vector.getElem_swap_right, Vector.getElem_swap_left] at h1 h2
    simp [*]; exact ih
  case case2 v_arr v_i v_j v_p v_q hpi hqr hli hij hjr hjq halgep haqltp j' isLtj' left2 hjpiv1 x1 hjpiv i' isLti' left1 left_ hapiv1 x2 hapiv h_iltj hqsimp hpsimp arr_1 h1 h2 arr_2 ih =>
    unfold classic.loop
    simp [arr_1, Vector.getElem_swap_right, Vector.getElem_swap_left] at h1 h2
    simp [*]; exact ih
  case case3 v_arr v_i v_j v_p v_q hpi hqr hli hij hjr hjq halgep haqltp j' isLtj' left2 hjpiv1 x1 hjpiv i' isLti' left1 left_ hapiv1 x2 hapiv h_iltj hqsimp hpsimp arr_1 h1 arr_2 h2 ih =>
    unfold classic.loop
    have hpj : j' ≠ v_p := by omega
    have hpji' : j' ≠ i' := by omega
    simp [arr_1, arr_2, Vector.getElem_swap_right, Vector.getElem_swap_left, Vector.getElem_swap_of_ne hpj hpji'] at h1 h2
    simp [*]; exact ih
  case case4 v_arr v_i v_j v_p v_q hpi hqr hli hij hjr hjq halgep haqltp j' isLtj' left2 hjpiv1 x1 hjpiv i' isLti' left1 left_ hapiv1 x2 hapiv h_iltj hqsimp hpsimp arr_1 h1 arr_2 h2 arr_3 ih =>
    unfold classic.loop
    have hpj : j' ≠ v_p := by omega
    have hpji' : j' ≠ i' := by omega
    simp [arr_1, arr_2, Vector.getElem_swap_right, Vector.getElem_swap_left, Vector.getElem_swap_of_ne hpj hpji'] at h1 h2
    simp [*]; exact ih
  case case5 v_arr v_i v_j v_p v_q hpi hqr hli hij hjr hjq halgep haqltp j' isLtj' left2 hjpiv1 x1 hjpiv i' isLti' left1 left_ hapiv1 x2 hapiv h1 hp h2 arr_1 j'' hj'' h_p arr_2 i'' hi'' h_q =>
    unfold classic.loop
    simp [*]
    have hj''_le := move_p_back_bounds h_p
    have hi''_le := move_q_forward_bounds h_q
    omega
  case case6 v_arr v_i v_j v_p v_q hpi hqr hli hij hjr hjq halgep haqltp j' isLtj' left2 hjpiv1 x1 hjpiv i' isLti' left1 left_ hapiv1 x2 hapiv h1 hp h2 arr_1 j'' hj'' h_p arr_2 i'' hi'' h_q =>
    unfold classic.loop
    simp [*]
    have hj''_le := move_p_back_bounds h_p
    have hi''_le := move_q_forward_bounds h_q
    omega

theorem Partition.bentleyMcIlroy.classic.partition_bounds [Ord α] [Std.TransOrd α] {arr : Vector α n} {left : Nat} {right : Nat} {hlr : left < right} {hr : right < n} : (Partition.bentleyMcIlroy.classic arr left right hlr hr).val.j' < (Partition.bentleyMcIlroy.classic arr left right hlr hr).val.i' := by
  unfold Partition.bentleyMcIlroy.classic
  simp only [Partition.bentleyMcIlroy.classic.loop.partition_bounds]

theorem Partition.bentleyMcIlroy.partition_bounds [Ord α] [Std.TransOrd α] {arr : Vector α n} {left : Nat} {right : Nat} {hlr : left < right} {hr : right < n} : (Partition.bentleyMcIlroy arr left right hlr hr).val.j' < (Partition.bentleyMcIlroy arr left right hlr hr).val.i' := by
  dsimp [Partition.bentleyMcIlroy]
  split
  · exact Partition.bentleyMcIlroy.classic.loop.partition_bounds
  · exact Partition.bentleyMcIlroy.eager.loop.partition_bounds

section qsort_bentleyMcIlroy

open Partition
open Array

variable [Ord α]

open Ord

theorem bentleyMcIlroy.permStabilizing {n : Nat} {left right : Nat}
    {hlr : left < right} {hr : right < n} (arr : Vector α n) :
    PermStabilizing' left right (Partition.bentleyMcIlroy arr left right hlr hr).val.arr' arr := by
  simp only [Partition.bentleyMcIlroy]; split
  any_goals simp only [panicWithPosWithDecl, panic, panicCore, *]
  all_goals
    apply PermStabilizing'.trans
    · try apply classic.loop.permStabilizing <;> omega
      try apply eager.loop.permStabilizing <;> omega
    · apply PermStabilizing'.trans
      · apply maybeSwap_permStabilizing <;> (simp only [Fin.val_mk] <;> omega)
      · apply PermStabilizing'.trans
        · apply maybeSwap_permStabilizing <;> (simp only [Fin.val_mk] <;> omega)
        · apply maybeSwap_permStabilizing <;> (simp only [Fin.val_mk] <;> omega)

theorem qsort_bentleyMcIlroy.sort.permStabilizing {as : Vector α n} {left right : Nat} {hsize' : right ≤ n - 1} : Vector.PermStabilizing' left right (sort as left right hsize') as := by
  induction as, left, right, hsize' using qsort_bentleyMcIlroy.sort.induct with
  | case1 as left right hsize' hlr as' j' i' hli hjr heq as'' ih1 ih2 =>
    unfold qsort_bentleyMcIlroy.sort; simp [*]
    have ih0 := heq ▸ bentleyMcIlroy.permStabilizing as (left := left) (right := right) (hlr := hlr) (hr := by omega)
    replace ih1 : Vector.PermStabilizing' left right .. := ih1.mono (by omega) (by omega)
    replace ih2 : Vector.PermStabilizing' left right .. := ih2.mono (by omega) (by omega)
    exact ih2 |>.trans ih1 |>.trans ih0
  | case2 as left right hsize' hlr =>
    unfold qsort_bentleyMcIlroy.sort; simp [*]
    apply Vector.PermStabilizing'.refl

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

theorem bentleyMcIlroy.classic.permStabilizing {n : Nat} {left right : Nat}
    {hlr : left < right} {hr : right < n} (arr : Vector α n) :
    PermStabilizing' left right (Partition.bentleyMcIlroy.classic arr left right hlr hr).val.arr' arr := by
  simp only [Partition.bentleyMcIlroy.classic]
  apply PermStabilizing'.trans
  · apply classic.loop.permStabilizing <;> omega
  · apply PermStabilizing'.trans
    · apply maybeSwap_permStabilizing <;> (simp only [Fin.val_mk] <;> omega)
    · apply PermStabilizing'.trans
      · apply maybeSwap_permStabilizing <;> (simp only [Fin.val_mk] <;> omega)
      · apply maybeSwap_permStabilizing <;> (simp only [Fin.val_mk] <;> omega)


theorem qsort_bentleyMcIlroy_strict.sort.permStabilizing {as : Vector α n} {left right : Nat} {hsize' : right ≤ n - 1} : Vector.PermStabilizing' left right (sort as left right hsize') as := by
  induction as, left, right, hsize' using qsort_bentleyMcIlroy_strict.sort.induct with
  | case1 as left right hsize' hlr as' j' i' hli hjr heq as'' ih1 ih2 =>
    unfold qsort_bentleyMcIlroy_strict.sort; simp [*]
    have ih0 := heq ▸ bentleyMcIlroy.classic.permStabilizing as (left := left) (right := right) (hlr := hlr) (hr := by omega)
    replace ih1 : Vector.PermStabilizing' left right .. := ih1.mono (by omega) (by omega)
    replace ih2 : Vector.PermStabilizing' left right .. := ih2.mono (by omega) (by omega)
    exact ih2 |>.trans ih1 |>.trans ih0
  | case2 as left right hsize' hlr =>
    unfold qsort_bentleyMcIlroy_strict.sort; simp [*]
    apply Vector.PermStabilizing'.refl

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
