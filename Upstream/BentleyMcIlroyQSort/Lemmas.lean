import Upstream.Init.RangeHas
import Upstream.Init.PermStabalizing

import Upstream.BentleyMcIlroyQSort.Basic
import Upstream.BentleyMcIlroyQSort.Lemmas_perm
import Upstream.BentleyMcIlroyQSort.Lemmas_moves

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

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


theorem bentleyMcIlroy.classic.while_i'_elem_not_left_of_piv [Ord α]
    {n : Nat} {left right : Nat} {hr : right < n} {pivot : α}
    {arr : Vector α n} {i j : Nat} {hjr : j < right}
    {ival : Nat} {hii : i ≤ ival} {hxi : ival ≤ right}
    {harltp : ¬lt arr[right] pivot} :
    ¬lt arr[(Partition.bentleyMcIlroy.classic.loop.while_i' left right hr pivot arr i j hjr ival hii hxi harltp).1.val] pivot := by
  induction ival, hii, hxi using Partition.bentleyMcIlroy.classic.loop.while_i'.induct right hr pivot arr i j harltp with
  | case1 ival hii hxi hi hlt hir ih =>
    unfold Partition.bentleyMcIlroy.classic.loop.while_i'; simp [*]
  | case2 ival hii hxi hi hle =>
    unfold Partition.bentleyMcIlroy.classic.loop.while_i'; simp [*]

theorem bentleyMcIlroy.classic.while_j'_elem_not_right_of_piv [Ord α]
    {n : Nat} {left right : Nat} {hr : right < n} {hl : left < n} {pivot : α}
    {arr : Vector α n} {i j : Nat} {hjr : j < right} {hli : left < i}
    {jval : Nat} {hxj : left ≤ jval} {hjj : jval ≤ j}
    {halgep : ¬lt pivot arr[left]} :
    ¬lt pivot arr[(Partition.bentleyMcIlroy.classic.loop.while_j' left right hr hl pivot arr i j hjr hli jval hxj hjj halgep).1.val] := by
  induction jval, hxj, hjj using Partition.bentleyMcIlroy.classic.loop.while_j'.induct left right hr hl pivot arr i j hjr halgep with
  | case1 jval hxj hjj hj hlt hjl ih =>
    unfold Partition.bentleyMcIlroy.classic.loop.while_j'; simp [*]
  | case2 jval hxj hjj hj  hle =>
    unfold Partition.bentleyMcIlroy.classic.loop.while_j'; simp [*]

theorem bentleyMcIlroy.classic.while_i'_before_is_left [Ord α]
    {n : Nat} {left right : Nat} {hr : right < n} {pivot : α}
    {arr : Vector α n} {i j : Nat} {hjr : j < right}
    {ival : Nat} {hii : i ≤ ival} {hxi : ival ≤ right}
    {harltp : ¬lt arr[right] pivot} :
    RangeHas n (lt arr[·] pivot) ival (Partition.bentleyMcIlroy.classic.loop.while_i' left right hr pivot arr i j hjr ival hii hxi harltp) := by
  induction ival, hii, hxi using Partition.bentleyMcIlroy.classic.loop.while_i'.induct right hr pivot arr i j harltp with
  | case1 ival hii hxi hi hlt hir ih =>
    unfold Partition.bentleyMcIlroy.classic.loop.while_i'; simp [*]
    apply RangeHas.prepend <;> grind [Ordering.isLT]
  | case2 ival hii hxi hi hle =>
    unfold Partition.bentleyMcIlroy.classic.loop.while_i'; simp [*]
    apply RangeHas.refl

theorem bentleyMcIlroy.classic.while_j'_before_is_right [Ord α]
    {n : Nat} {left right : Nat} {hr : right < n} {hl : left < n} {pivot : α}
    {arr : Vector α n} {i j : Nat} {hjr : j < right} {hli : left < i}
    {jval : Nat} {hxj : left ≤ jval} {hjj : jval ≤ j}
    {halgep : ¬lt pivot arr[left]} :
    RangeHas n (lt pivot arr[·]) ((Partition.bentleyMcIlroy.classic.loop.while_j' left right hr hl pivot arr i j hjr hli jval hxj hjj halgep) + 1) (jval + 1) := by
  induction jval, hxj, hjj using Partition.bentleyMcIlroy.classic.loop.while_j'.induct left right hr hl pivot arr i j hjr halgep with
  | case1 jval hxj hjj hj hlt hjl ih =>
    unfold Partition.bentleyMcIlroy.classic.loop.while_j'; simp [*]
    replace ih := show (jval - 1 + 1) = jval by omega ▸ ih
    apply RangeHas.append <;> grind [Ordering.isLT]
  | case2 jval hxj hjj hj hle =>
    unfold Partition.bentleyMcIlroy.classic.loop.while_j'; simp [*]
    apply RangeHas.refl

private theorem bentleyMcIlroy.classic.while_i'_extends_left
    [Ord α] [Std.TransOrd α]
    {n left right start : Nat} {hr : right < n} {pivot : α}
    {arr : Vector α n} {i j : Nat} {hjr : j < right}
    {ival : Nat} {hii : i ≤ ival} {hxi : ival ≤ right}
    {harltp : ¬lt arr[right] pivot}
    (H : RangeHas n (¬lt pivot arr[·]) start ival) :
    RangeHas n (¬lt pivot arr[·]) start
      (Partition.bentleyMcIlroy.classic.loop.while_i'
        left right hr pivot arr i j hjr ival hii hxi harltp).1.val := by
  have lt_asymm : ∀ {x y : α}, lt x y → ¬lt y x := by grind
  apply RangeHas.trans H
  intro x hx1 hx2
  exact lt_asymm (bentleyMcIlroy.classic.while_i'_before_is_left
    (hr := hr) (arr := arr) (i := i) (j := j) (ival := ival) x hx1 hx2)

private theorem bentleyMcIlroy.classic.while_j'_extends_right
    [Ord α] [Std.TransOrd α]
    {n left right top : Nat} {hr : right < n} {hl : left < n} {pivot : α}
    {arr : Vector α n} {i j : Nat} {hjr : j < right} {hli : left < i}
    {jval : Nat} {hxj : left ≤ jval} {hjj : jval ≤ j}
    {halgep : ¬lt pivot arr[left]}
    (H : RangeHas n (¬lt arr[·] pivot) (jval + 1) top) :
    RangeHas n (¬lt arr[·] pivot)
      ((Partition.bentleyMcIlroy.classic.loop.while_j'
        left right hr hl pivot arr i j hjr hli jval hxj hjj halgep).1.val + 1) top := by
  have lt_asymm : ∀ {x y : α}, lt x y → ¬lt y x := by grind
  apply RangeHas.trans
  · intro x hx1 hx2
    exact lt_asymm (bentleyMcIlroy.classic.while_j'_before_is_right
      (hr := hr) (hl := hl) (arr := arr) (i := i) (j := j)
      (jval := jval) x hx1 hx2)
  · exact H

private theorem RangeHas.swap_before {n i j a b : Nat} {arr : Vector α n}
    {hi : i < n} {hj : j < n} {pred : α → Prop}
    (H : RangeHas n (pred arr[·]) a b) (hbi : b ≤ i) (hbj : b ≤ j) :
    RangeHas n (pred (arr.swap i j hi hj)[·]) a b := by
  intro x hx1 hx2
  have hxi : x.val ≠ i := by omega
  have hxj : x.val ≠ j := by omega
  rw [show (arr.swap i j hi hj)[x] = arr[x] by
    apply Vector.getElem_swap_of_ne <;> assumption]
  exact H x hx1 hx2

private theorem RangeHas.swap_after {n i j a b : Nat} {arr : Vector α n}
    {hi : i < n} {hj : j < n} {pred : α → Prop}
    (H : RangeHas n (pred arr[·]) a b) (hia : i < a) (hja : j < a) :
    RangeHas n (pred (arr.swap i j hi hj)[·]) a b := by
  intro x hx1 hx2
  have hxi : x.val ≠ i := by omega
  have hxj : x.val ≠ j := by omega
  rw [show (arr.swap i j hi hj)[x] = arr[x] by
    apply Vector.getElem_swap_of_ne <;> assumption]
  exact H x hx1 hx2

private theorem RangeHas.swap_of_pred {n i j a b : Nat} {arr : Vector α n}
    {hi : i < n} {hj : j < n} {pred : α → Prop}
    (H : RangeHas n (pred arr[·]) a b)
    (Hi : pred arr[(⟨i, hi⟩ : Fin n)]) (Hj : pred arr[(⟨j, hj⟩ : Fin n)]) :
    RangeHas n (pred (arr.swap i j hi hj)[·]) a b := by
  intro x hx1 hx2
  if hxi : x.val = i then
    simpa only [hxi, Fin.getElem_fin, Vector.getElem_swap_left] using Hj
  else if hxj : x.val = j then
    simpa only [hxj, Fin.getElem_fin, Vector.getElem_swap_right] using Hi
  else
    rw [show (arr.swap i j hi hj)[x] = arr[x] by
      apply Vector.getElem_swap_of_ne <;> assumption]
    exact H x hx1 hx2

private theorem Partition.bentleyMcIlroy.move_pivots_back.sorted
    [Ord α] {n left right p q i j lowStart highEnd : Nat}
    {pivot : α} {arr : Vector α n}
    {hr : right < n} {hjr : j < right} {hli : left < i}
    (hji : j < i) (hpj : p ≤ j + 1) (hlp : left + 1 ≤ p)
    (hiq : i ≤ q + 1) (hqr : q < right)
    (hlo : lowStart ≤ left + 1) (hhi : right ≤ highEnd)
    (H_left : RangeHas n (¬lt pivot arr[·]) lowStart i)
    (H_right : RangeHas n (¬lt arr[·] pivot) (j + 1) highEnd)
    (H_p : RangeHas n (¬lt arr[·] pivot) (left + 1) p)
    (H_q : RangeHas n (¬lt pivot arr[·]) (q + 1) right) :
    let hp : p < n := by omega
    let movedP := move_p_back hr hp (left + 1) arr j hjr
    let movedQ := move_q_forward hr hiq (q + 1)
      movedP.1 i (Nat.le_refl _) hli (by omega : i = q + 1 - (q + 1) + i)
    RangeHas n (¬lt pivot movedQ.1[·]) lowStart movedQ.2.val ∧
      RangeHas n (¬lt movedQ.1[·] pivot) (movedP.2.val + 1) highEnd := by
  have hp : p < n := by omega
  let movedP := move_p_back hr hp (left + 1) arr j hjr
  have H_left_source : RangeHas n (¬lt pivot arr[·]) (left + 1) p :=
    RangeHas.mono H_left hlo (by omega)
  have H_p_low_fill :
      RangeHas n (¬lt pivot movedP.1[·]) (movedP.2.val + 1) (j + 1) := by
    exact move_p_back_fills (hr := hr) (hp := hp) (hjr := hjr)
      (pred := fun a ↦ ¬lt pivot a)
      (hkpos := by omega) (hkp := hlp) (hpj := hpj) H_left_source
  have H_p_high_fill :
      RangeHas n (¬lt movedP.1[·] pivot) (movedP.2.val + 1) (j + 1) := by
    exact move_p_back_fills (hr := hr) (hp := hp) (hjr := hjr)
      (pred := fun a ↦ ¬lt a pivot)
      (hkpos := by omega) (hkp := hlp) (hpj := hpj) H_p
  have H_p_low_before :
      RangeHas n (¬lt pivot movedP.1[·]) lowStart (movedP.2.val + 1) := by
    have hpreserve := move_p_back_preserves
      (left := lowStart) (right := right) (p := p) (k := left + 1)
      (arr := arr) (j := j) (j_orig := j) (pivot := pivot)
      (hr := hr) (hp := hp) (hjr := hjr)
      (Nat.le_refl j) hlo hpj (by omega)
      (fun x hx1 hx2 ↦ H_left x hx1 (by omega))
    dsimp only [movedP]
    intro x hx1 hx2
    exact hpreserve x hx1 (by omega)
  have H_p_low_through_j :
      RangeHas n (¬lt pivot movedP.1[·]) lowStart (j + 1) :=
    RangeHas.trans H_p_low_before H_p_low_fill
  have H_p_low_after : RangeHas n (¬lt pivot movedP.1[·]) (j + 1) i := by
    intro x hx1 hx2
    rw [move_p_back_eq_after (hr := hr) (hp := hp) (hjr := hjr)
      (hjj := Nat.le_refl j) (hpj := hpj) x (by omega)]
    exact H_left x (by omega) hx2
  have H_p_low : RangeHas n (¬lt pivot movedP.1[·]) lowStart i :=
    RangeHas.trans H_p_low_through_j H_p_low_after
  have H_p_high_after :
      RangeHas n (¬lt movedP.1[·] pivot) (j + 1) highEnd := by
    intro x hx1 hx2
    rw [move_p_back_eq_after (hr := hr) (hp := hp) (hjr := hjr)
      (hjj := Nat.le_refl j) (hpj := hpj) x (by omega)]
    exact H_right x hx1 hx2
  have H_p_high :
      RangeHas n (¬lt movedP.1[·] pivot) (movedP.2.val + 1) highEnd :=
    RangeHas.trans H_p_high_fill H_p_high_after
  have H_q_low_source : RangeHas n (¬lt pivot movedP.1[·]) (q + 1) right := by
    intro x hx1 hx2
    rw [move_p_back_eq_after (hr := hr) (hp := hp) (hjr := hjr)
      (hjj := Nat.le_refl j) (hpj := hpj) x (by omega)]
    exact H_q x hx1 hx2
  have H_q_high_source : RangeHas n (¬lt movedP.1[·] pivot) (q + 1) right :=
    RangeHas.mono H_p_high_after (by omega) hhi
  let movedQ := move_q_forward hr hiq (q + 1) movedP.1 i
    (Nat.le_refl _) hli (by omega : i = q + 1 - (q + 1) + i)
  have H_q_low_fill : RangeHas n (¬lt pivot movedQ.1[·]) i movedQ.2.val := by
    exact move_q_forward_fills
      (left := left) (right := right) (q := q) (k := q + 1)
      (arr := movedP.1) (i := i) (i' := i) (hr := hr) (hi'q := hiq)
      (pred := fun a ↦ ¬lt pivot a) H_q_low_source
  have H_q_high_fill : RangeHas n (¬lt movedQ.1[·] pivot) i movedQ.2.val := by
    exact move_q_forward_fills
      (left := left) (right := right) (q := q) (k := q + 1)
      (arr := movedP.1) (i := i) (i' := i) (hr := hr) (hi'q := hiq)
      (pred := fun a ↦ ¬lt a pivot) H_q_high_source
  have H_q_low_before : RangeHas n (¬lt pivot movedQ.1[·]) lowStart i := by
    intro x hx1 hx2
    rw [move_q_forward_eq_before (hr := hr) (hi'q := hiq) x hx2]
    exact H_p_low x hx1 (by omega)
  have H_q_low : RangeHas n (¬lt pivot movedQ.1[·]) lowStart movedQ.2.val :=
    RangeHas.trans H_q_low_before H_q_low_fill
  have H_q_high_before :
      RangeHas n (¬lt movedQ.1[·] pivot) (movedP.2.val + 1) i := by
    intro x hx1 hx2
    rw [move_q_forward_eq_before (hr := hr) (hi'q := hiq) x hx2]
    exact H_p_high x hx1 (by omega)
  have H_q_high_after :
      RangeHas n (¬lt movedQ.1[·] pivot) movedQ.2.val highEnd := by
    exact move_q_forward_preserves_range
      (left := left) (right := right) (q := q) (k := q + 1)
      (top := highEnd)
      (arr := movedP.1) (i := i) (i' := i) (hr := hr) (hi'q := hiq)
      (pred := fun a ↦ ¬lt a pivot) hhi
      (RangeHas.mono H_p_high_after (by omega) (Nat.le_refl highEnd))
  have H_q_high :
      RangeHas n (¬lt movedQ.1[·] pivot) (movedP.2.val + 1) highEnd :=
    RangeHas.trans H_q_high_before (RangeHas.trans H_q_high_fill H_q_high_after)
  dsimp only
  constructor
  · exact H_q_low
  · exact H_q_high

set_option maxHeartbeats 1200000 in
theorem Partition.bentleyMcIlroy.classic.loop.sorted [Ord α] [Std.TransOrd α]
    {left right : Nat} {hr : right < n} {hl : left < n} {pivot : α}
    {arr : Vector α n} {i j p q : Nat} {hpi : p ≤ i} {hqr : q < right}
    {hli : left < i} {hij : i ≤ j + 1} {hjr : j < right} {hjq : j ≤ q}
    {halgep : ¬lt pivot arr[p - 1]} {haqltp : ¬lt arr[q + 1] pivot}
    (hlp : left + 1 ≤ p)
    (H_left : RangeHas n (¬lt pivot arr[·]) left i)
    (H_right : RangeHas n (¬lt arr[·] pivot) (j + 1) (right + 1))
    (H_p : RangeHas n (¬lt arr[·] pivot) (left + 1) p)
    (H_q : RangeHas n (¬lt pivot arr[·]) (q + 1) right) :
    IsPartitioned left right pivot
      (Partition.bentleyMcIlroy.classic.loop left right hr hl pivot arr i j p q
        hpi hqr hli hij hjr hjq halgep haqltp).val := by
  have lt_asymm : ∀ {x y : α}, lt x y → ¬lt y x := by grind
  induction arr, i, j, p, q, hpi, hqr, hli, hij, hjr, hjq, halgep, haqltp using
      classic.loop.induct left right hr hl pivot with
  | case1 v_arr v_i v_j v_p v_q hpi hqr hli hij hjr hjq halgep haqltp
      j' isLtj' left2 hjpiv1 x1 hjpiv i' isLti' left1 left_ hapiv1 x2 hapiv
      h_iltj hqsimp hpsimp arr_1 h1 h2 ih =>
      have H_left_scan : RangeHas n (¬lt pivot v_arr[·]) left i' := by
        have hs := bentleyMcIlroy.classic.while_i'_extends_left
          (left := left) (right := v_q + 1) (start := left)
          (arr := v_arr) (i := v_i) (j := j') (ival := v_i)
          (hr := by omega) (hjr := by omega) (hii := Nat.le_refl _)
          (hxi := by omega) (harltp := haqltp) H_left
        simpa only [x2] using hs
      have H_right_scan :
          RangeHas n (¬lt v_arr[·] pivot) (j' + 1) (right + 1) := by
        have hs := bentleyMcIlroy.classic.while_j'_extends_right
          (left := v_p - 1) (right := right) (top := right + 1)
          (arr := v_arr) (i := v_i) (j := v_j) (jval := v_j)
          (hr := hr) (hl := by omega) (hjr := hjr) (hli := by omega)
          (hxj := by omega) (hjj := Nat.le_refl _) (halgep := halgep) H_right
        simpa only [x1] using hs
      have H_left_arr_1 : RangeHas n (¬lt pivot arr_1[·]) left i' := by
        simpa only [arr_1] using
          (RangeHas.swap_before (n := n) (arr := v_arr) (i := i') (j := j')
            (pred := fun a ↦ ¬lt pivot a) H_left_scan (Nat.le_refl i') (by omega))
      have H_right_arr_1 :
          RangeHas n (¬lt arr_1[·] pivot) (j' + 1) (right + 1) := by
        simpa only [arr_1] using
          (RangeHas.swap_after (n := n) (arr := v_arr) (i := i') (j := j')
            (pred := fun a ↦ ¬lt a pivot) H_right_scan
            (by omega) (Nat.lt_succ_self j'))
      have H_p_arr_1 : RangeHas n (¬lt arr_1[·] pivot) (left + 1) v_p := by
        simpa only [arr_1] using
          (RangeHas.swap_before (n := n) (arr := v_arr) (i := i') (j := j')
            (pred := fun a ↦ ¬lt a pivot) H_p (by omega) (by omega))
      have H_q_arr_1 : RangeHas n (¬lt pivot arr_1[·]) (v_q + 1) right := by
        simpa only [arr_1] using
          (RangeHas.swap_after (n := n) (arr := v_arr) (i := i') (j := j')
            (pred := fun a ↦ ¬lt pivot a) H_q (by omega) (by omega))
      dsimp only [arr_1] at h1 h2
      unfold classic.loop
      simp only [x1, x2, dif_pos h_iltj, dif_pos h1, dif_pos h2]
      apply ih hlp
      · apply RangeHas.append (n := n) (a := left) (b := i') (hb := isLti')
          (pred := fun x ↦ ¬lt pivot arr_1[x])
        · simpa only [Fin.getElem_fin] using lt_asymm h1
        · exact H_left_arr_1
      · have hjpred : j' - 1 + 1 = j' := by omega
        rw [hjpred]
        apply RangeHas.prepend (n := n) (a := j') (b := right + 1) (ha := isLtj')
          (pred := fun x ↦ ¬lt arr_1[x] pivot)
        · simpa only [Fin.getElem_fin] using lt_asymm h2
        · exact H_right_arr_1
      · exact H_p_arr_1
      · exact H_q_arr_1
  | case2 v_arr v_i v_j v_p v_q hpi hqr hli hij hjr hjq halgep haqltp
      j' isLtj' left2 hjpiv1 x1 hjpiv i' isLti' left1 left_ hapiv1 x2 hapiv
      h_iltj hqsimp hpsimp arr_1 h1 h2 arr_2 ih =>
      have H_left_scan : RangeHas n (¬lt pivot v_arr[·]) left i' := by
        have hs := bentleyMcIlroy.classic.while_i'_extends_left
          (left := left) (right := v_q + 1) (start := left)
          (arr := v_arr) (i := v_i) (j := j') (ival := v_i)
          (hr := by omega) (hjr := by omega) (hii := Nat.le_refl _)
          (hxi := by omega) (harltp := haqltp) H_left
        simpa only [x2] using hs
      have H_right_scan :
          RangeHas n (¬lt v_arr[·] pivot) (j' + 1) (right + 1) := by
        have hs := bentleyMcIlroy.classic.while_j'_extends_right
          (left := v_p - 1) (right := right) (top := right + 1)
          (arr := v_arr) (i := v_i) (j := v_j) (jval := v_j)
          (hr := hr) (hl := by omega) (hjr := hjr) (hli := by omega)
          (hxj := by omega) (hjj := Nat.le_refl _) (halgep := halgep) H_right
        simpa only [x1] using hs
      have hq_n : v_q < n := by omega
      have H_left_arr_1 : RangeHas n (¬lt pivot arr_1[·]) left i' := by
        simpa only [arr_1] using
          (RangeHas.swap_before (n := n) (arr := v_arr) (i := i') (j := j')
            (pred := fun a ↦ ¬lt pivot a) H_left_scan (Nat.le_refl i') (by omega))
      have H_left_arr_1_plus : RangeHas n (¬lt pivot arr_1[·]) left (i' + 1) := by
        apply RangeHas.append (n := n) (a := left) (b := i') (hb := isLti')
          (pred := fun x ↦ ¬lt pivot arr_1[x])
        · simpa only [Fin.getElem_fin] using lt_asymm h1
        · exact H_left_arr_1
      have H_left_arr_2 : RangeHas n (¬lt pivot arr_2[·]) left (i' + 1) := by
        simpa only [arr_2] using
          (RangeHas.swap_before (n := n) (arr := arr_1) (i := v_q) (j := j')
            (pred := fun a ↦ ¬lt pivot a) H_left_arr_1_plus (by omega) (by omega))
      have H_p_arr_1 : RangeHas n (¬lt arr_1[·] pivot) (left + 1) v_p := by
        simpa only [arr_1] using
          (RangeHas.swap_before (n := n) (arr := v_arr) (i := i') (j := j')
            (pred := fun a ↦ ¬lt a pivot) H_p (by omega) (by omega))
      have H_p_arr_2 : RangeHas n (¬lt arr_2[·] pivot) (left + 1) v_p := by
        simpa only [arr_2] using
          (RangeHas.swap_before (n := n) (arr := arr_1) (i := v_q) (j := j')
            (pred := fun a ↦ ¬lt a pivot) H_p_arr_1 (by omega) (by omega))
      have H_right_tail_arr_1 :
          RangeHas n (¬lt arr_1[·] pivot) (j' + 1) (right + 1) := by
        simpa only [arr_1] using
          (RangeHas.swap_after (n := n) (arr := v_arr) (i := i') (j := j')
            (pred := fun a ↦ ¬lt a pivot) H_right_scan
            (by omega) (Nat.lt_succ_self j'))
      have H_j_high_arr_1 : ¬lt arr_1[(⟨j', isLtj'⟩ : Fin n)] pivot := by
        simpa only [arr_1, Fin.getElem_fin, Vector.getElem_swap_right] using hapiv
      have H_right_arr_1 : RangeHas n (¬lt arr_1[·] pivot) j' (right + 1) := by
        apply RangeHas.prepend (n := n) (a := j') (b := right + 1) (ha := isLtj')
          (pred := fun x ↦ ¬lt arr_1[x] pivot)
        · exact H_j_high_arr_1
        · exact H_right_tail_arr_1
      have H_q_high_arr_1 : ¬lt arr_1[(⟨v_q, hq_n⟩ : Fin n)] pivot :=
        H_right_arr_1 ⟨v_q, hq_n⟩ (Nat.le_trans left2 hjq) (Nat.lt_succ_of_lt hqr)
      have H_right_arr_2 : RangeHas n (¬lt arr_2[·] pivot) j' (right + 1) := by
        simpa only [arr_2] using
          (RangeHas.swap_of_pred (n := n) (arr := arr_1) (i := v_q) (j := j')
            (pred := fun a ↦ ¬lt a pivot) H_right_arr_1 H_q_high_arr_1 H_j_high_arr_1)
      have H_q_tail_arr_1 : RangeHas n (¬lt pivot arr_1[·]) (v_q + 1) right := by
        simpa only [arr_1] using
          (RangeHas.swap_after (n := n) (arr := v_arr) (i := i') (j := j')
            (pred := fun a ↦ ¬lt pivot a) H_q (by omega) (by omega))
      have H_q_tail_arr_2 : RangeHas n (¬lt pivot arr_2[·]) (v_q + 1) right := by
        simpa only [arr_2] using
          (RangeHas.swap_after (n := n) (arr := arr_1) (i := v_q) (j := j')
            (pred := fun a ↦ ¬lt pivot a) H_q_tail_arr_1
            (Nat.lt_succ_self v_q) (by omega))
      have H_q_arr_2 : RangeHas n (¬lt pivot arr_2[·]) v_q right := by
        apply RangeHas.prepend (n := n) (a := v_q) (b := right) (ha := hq_n)
          (pred := fun x ↦ ¬lt pivot arr_2[x])
        · simpa only [arr_2, Fin.getElem_fin, Vector.getElem_swap_left] using h2
        · exact H_q_tail_arr_2
      dsimp only [arr_1] at h1 h2
      unfold classic.loop
      simp only [x1, x2, dif_pos h_iltj, dif_pos h1, dif_neg h2]
      apply ih hlp H_left_arr_2
      · simpa only [show j' - 1 + 1 = j' by omega] using H_right_arr_2
      · exact H_p_arr_2
      · simpa only [hqsimp] using H_q_arr_2
  | case3 v_arr v_i v_j v_p v_q hpi hqr hli hij hjr hjq halgep haqltp
      j' isLtj' left2 hjpiv1 x1 hjpiv i' isLti' left1 left_ hapiv1 x2 hapiv
      h_iltj hqsimp hpsimp arr_1 h1 arr_2 h2 ih =>
      have H_left_scan : RangeHas n (¬lt pivot v_arr[·]) left i' := by
        have hs := bentleyMcIlroy.classic.while_i'_extends_left
          (left := left) (right := v_q + 1) (start := left)
          (arr := v_arr) (i := v_i) (j := j') (ival := v_i)
          (hr := by omega) (hjr := by omega) (hii := Nat.le_refl _)
          (hxi := by omega) (harltp := haqltp) H_left
        simpa only [x2] using hs
      have H_right_scan :
          RangeHas n (¬lt v_arr[·] pivot) (j' + 1) (right + 1) := by
        have hs := bentleyMcIlroy.classic.while_j'_extends_right
          (left := v_p - 1) (right := right) (top := right + 1)
          (arr := v_arr) (i := v_i) (j := v_j) (jval := v_j)
          (hr := hr) (hl := by omega) (hjr := hjr) (hli := by omega)
          (hxj := by omega) (hjj := Nat.le_refl _) (halgep := halgep) H_right
        simpa only [x1] using hs
      have hp_n : v_p < n := by omega
      have H_left_arr_1 : RangeHas n (¬lt pivot arr_1[·]) left i' := by
        simpa only [arr_1] using
          (RangeHas.swap_before (n := n) (arr := v_arr) (i := i') (j := j')
            (pred := fun a ↦ ¬lt pivot a) H_left_scan (Nat.le_refl i') (by omega))
      have H_i_low_arr_1 : ¬lt pivot arr_1[(⟨i', isLti'⟩ : Fin n)] := by
        simpa only [arr_1, Fin.getElem_fin, Vector.getElem_swap_left] using hjpiv
      have H_left_arr_1_plus : RangeHas n (¬lt pivot arr_1[·]) left (i' + 1) := by
        apply RangeHas.append (n := n) (a := left) (b := i') (hb := isLti')
          (pred := fun x ↦ ¬lt pivot arr_1[x])
        · exact H_i_low_arr_1
        · exact H_left_arr_1
      have H_p_low_arr_1 : ¬lt pivot arr_1[(⟨v_p, hp_n⟩ : Fin n)] :=
        H_left_arr_1_plus ⟨v_p, hp_n⟩
          (Nat.le_trans (Nat.le_succ left) hlp)
          (Nat.lt_succ_of_le (Nat.le_trans hpi left1))
      have H_left_arr_2 : RangeHas n (¬lt pivot arr_2[·]) left (i' + 1) := by
        simpa only [arr_2] using
          (RangeHas.swap_of_pred (n := n) (arr := arr_1) (i := v_p) (j := i')
            (pred := fun a ↦ ¬lt pivot a) H_left_arr_1_plus H_p_low_arr_1 H_i_low_arr_1)
      have H_p_arr_1 : RangeHas n (¬lt arr_1[·] pivot) (left + 1) v_p := by
        simpa only [arr_1] using
          (RangeHas.swap_before (n := n) (arr := v_arr) (i := i') (j := j')
            (pred := fun a ↦ ¬lt a pivot) H_p (by omega) (by omega))
      have H_p_before_arr_2 : RangeHas n (¬lt arr_2[·] pivot) (left + 1) v_p := by
        simpa only [arr_2] using
          (RangeHas.swap_before (n := n) (arr := arr_1) (i := v_p) (j := i')
            (pred := fun a ↦ ¬lt a pivot) H_p_arr_1 (Nat.le_refl v_p) (by omega))
      have H_p_arr_2 : RangeHas n (¬lt arr_2[·] pivot) (left + 1) (v_p + 1) := by
        apply RangeHas.append (n := n) (a := left + 1) (b := v_p) (hb := hp_n)
          (pred := fun x ↦ ¬lt arr_2[x] pivot)
        · simpa only [arr_2, Fin.getElem_fin, Vector.getElem_swap_left] using h1
        · exact H_p_before_arr_2
      have H_right_arr_1 :
          RangeHas n (¬lt arr_1[·] pivot) (j' + 1) (right + 1) := by
        simpa only [arr_1] using
          (RangeHas.swap_after (n := n) (arr := v_arr) (i := i') (j := j')
            (pred := fun a ↦ ¬lt a pivot) H_right_scan
            (by omega) (Nat.lt_succ_self j'))
      have H_right_tail_arr_2 :
          RangeHas n (¬lt arr_2[·] pivot) (j' + 1) (right + 1) := by
        simpa only [arr_2] using
          (RangeHas.swap_after (n := n) (arr := arr_1) (i := v_p) (j := i')
            (pred := fun a ↦ ¬lt a pivot) H_right_arr_1 (by omega) (by omega))
      have H_right_arr_2 : RangeHas n (¬lt arr_2[·] pivot) j' (right + 1) := by
        apply RangeHas.prepend (n := n) (a := j') (b := right + 1) (ha := isLtj')
          (pred := fun x ↦ ¬lt arr_2[x] pivot)
        · simpa only [Fin.getElem_fin] using lt_asymm h2
        · exact H_right_tail_arr_2
      have H_q_arr_1 : RangeHas n (¬lt pivot arr_1[·]) (v_q + 1) right := by
        simpa only [arr_1] using
          (RangeHas.swap_after (n := n) (arr := v_arr) (i := i') (j := j')
            (pred := fun a ↦ ¬lt pivot a) H_q (by omega) (by omega))
      have H_q_arr_2 : RangeHas n (¬lt pivot arr_2[·]) (v_q + 1) right := by
        simpa only [arr_2] using
          (RangeHas.swap_after (n := n) (arr := arr_1) (i := v_p) (j := i')
            (pred := fun a ↦ ¬lt pivot a) H_q_arr_1 (by omega) (by omega))
      dsimp only [arr_1, arr_2] at h1 h2
      unfold classic.loop
      simp only [x1, x2, dif_pos h_iltj, dif_neg h1, dif_pos h2]
      apply ih (by omega) H_left_arr_2
      · simpa only [show j' - 1 + 1 = j' by omega] using H_right_arr_2
      · exact H_p_arr_2
      · exact H_q_arr_2
  | case4 v_arr v_i v_j v_p v_q hpi hqr hli hij hjr hjq halgep haqltp
      j' isLtj' left2 hjpiv1 x1 hjpiv i' isLti' left1 left_ hapiv1 x2 hapiv
      h_iltj hqsimp hpsimp arr_1 h1 arr_2 h2 arr_3 ih =>
      have H_left_scan : RangeHas n (¬lt pivot v_arr[·]) left i' := by
        have hs := bentleyMcIlroy.classic.while_i'_extends_left
          (left := left) (right := v_q + 1) (start := left)
          (arr := v_arr) (i := v_i) (j := j') (ival := v_i)
          (hr := by omega) (hjr := by omega) (hii := Nat.le_refl _)
          (hxi := by omega) (harltp := haqltp) H_left
        simpa only [x2] using hs
      have H_right_scan :
          RangeHas n (¬lt v_arr[·] pivot) (j' + 1) (right + 1) := by
        have hs := bentleyMcIlroy.classic.while_j'_extends_right
          (left := v_p - 1) (right := right) (top := right + 1)
          (arr := v_arr) (i := v_i) (j := v_j) (jval := v_j)
          (hr := hr) (hl := by omega) (hjr := hjr) (hli := by omega)
          (hxj := by omega) (hjj := Nat.le_refl _) (halgep := halgep) H_right
        simpa only [x1] using hs
      have hp_n : v_p < n := by omega
      have hq_n : v_q < n := by omega
      have H_left_arr_1 : RangeHas n (¬lt pivot arr_1[·]) left i' := by
        simpa only [arr_1] using
          (RangeHas.swap_before (n := n) (arr := v_arr) (i := i') (j := j')
            (pred := fun a ↦ ¬lt pivot a) H_left_scan (Nat.le_refl i') (by omega))
      have H_i_low_arr_1 : ¬lt pivot arr_1[(⟨i', isLti'⟩ : Fin n)] := by
        simpa only [arr_1, Fin.getElem_fin, Vector.getElem_swap_left] using hjpiv
      have H_left_arr_1_plus : RangeHas n (¬lt pivot arr_1[·]) left (i' + 1) := by
        apply RangeHas.append (n := n) (a := left) (b := i') (hb := isLti')
          (pred := fun x ↦ ¬lt pivot arr_1[x])
        · exact H_i_low_arr_1
        · exact H_left_arr_1
      have H_p_low_arr_1 : ¬lt pivot arr_1[(⟨v_p, hp_n⟩ : Fin n)] :=
        H_left_arr_1_plus ⟨v_p, hp_n⟩
          (Nat.le_trans (Nat.le_succ left) hlp)
          (Nat.lt_succ_of_le (Nat.le_trans hpi left1))
      have H_left_arr_2 : RangeHas n (¬lt pivot arr_2[·]) left (i' + 1) := by
        simpa only [arr_2] using
          (RangeHas.swap_of_pred (n := n) (arr := arr_1) (i := v_p) (j := i')
            (pred := fun a ↦ ¬lt pivot a) H_left_arr_1_plus H_p_low_arr_1 H_i_low_arr_1)
      have H_left_arr_3 : RangeHas n (¬lt pivot arr_3[·]) left (i' + 1) := by
        simpa only [arr_3] using
          (RangeHas.swap_before (n := n) (arr := arr_2) (i := v_q) (j := j')
            (pred := fun a ↦ ¬lt pivot a) H_left_arr_2 (by omega) (by omega))
      have H_p_arr_1 : RangeHas n (¬lt arr_1[·] pivot) (left + 1) v_p := by
        simpa only [arr_1] using
          (RangeHas.swap_before (n := n) (arr := v_arr) (i := i') (j := j')
            (pred := fun a ↦ ¬lt a pivot) H_p (by omega) (by omega))
      have H_p_before_arr_2 : RangeHas n (¬lt arr_2[·] pivot) (left + 1) v_p := by
        simpa only [arr_2] using
          (RangeHas.swap_before (n := n) (arr := arr_1) (i := v_p) (j := i')
            (pred := fun a ↦ ¬lt a pivot) H_p_arr_1 (Nat.le_refl v_p) (by omega))
      have H_p_arr_2 : RangeHas n (¬lt arr_2[·] pivot) (left + 1) (v_p + 1) := by
        apply RangeHas.append (n := n) (a := left + 1) (b := v_p) (hb := hp_n)
          (pred := fun x ↦ ¬lt arr_2[x] pivot)
        · simpa only [arr_2, Fin.getElem_fin, Vector.getElem_swap_left] using h1
        · exact H_p_before_arr_2
      have H_p_arr_3 : RangeHas n (¬lt arr_3[·] pivot) (left + 1) (v_p + 1) := by
        simpa only [arr_3] using
          (RangeHas.swap_before (n := n) (arr := arr_2) (i := v_q) (j := j')
            (pred := fun a ↦ ¬lt a pivot) H_p_arr_2 (by omega) (by omega))
      have H_right_arr_1 :
          RangeHas n (¬lt arr_1[·] pivot) (j' + 1) (right + 1) := by
        simpa only [arr_1] using
          (RangeHas.swap_after (n := n) (arr := v_arr) (i := i') (j := j')
            (pred := fun a ↦ ¬lt a pivot) H_right_scan
            (by omega) (Nat.lt_succ_self j'))
      have H_right_tail_arr_2 :
          RangeHas n (¬lt arr_2[·] pivot) (j' + 1) (right + 1) := by
        simpa only [arr_2] using
          (RangeHas.swap_after (n := n) (arr := arr_1) (i := v_p) (j := i')
            (pred := fun a ↦ ¬lt a pivot) H_right_arr_1 (by omega) (by omega))
      have H_j_high_arr_2 : ¬lt arr_2[(⟨j', isLtj'⟩ : Fin n)] pivot := by
        simp only [arr_2, Fin.getElem_fin,
          Vector.getElem_swap_of_ne (show j' ≠ v_p by omega) (show j' ≠ i' by omega)]
        simpa only [arr_1, Vector.getElem_swap_right] using hapiv
      have H_right_arr_2 : RangeHas n (¬lt arr_2[·] pivot) j' (right + 1) := by
        apply RangeHas.prepend (n := n) (a := j') (b := right + 1) (ha := isLtj')
          (pred := fun x ↦ ¬lt arr_2[x] pivot)
        · exact H_j_high_arr_2
        · exact H_right_tail_arr_2
      have H_q_high_arr_2 : ¬lt arr_2[(⟨v_q, hq_n⟩ : Fin n)] pivot :=
        H_right_arr_2 ⟨v_q, hq_n⟩ (Nat.le_trans left2 hjq) (Nat.lt_succ_of_lt hqr)
      have H_right_arr_3 : RangeHas n (¬lt arr_3[·] pivot) j' (right + 1) := by
        simpa only [arr_3] using
          (RangeHas.swap_of_pred (n := n) (arr := arr_2) (i := v_q) (j := j')
            (pred := fun a ↦ ¬lt a pivot) H_right_arr_2 H_q_high_arr_2 H_j_high_arr_2)
      have H_q_arr_1 : RangeHas n (¬lt pivot arr_1[·]) (v_q + 1) right := by
        simpa only [arr_1] using
          (RangeHas.swap_after (n := n) (arr := v_arr) (i := i') (j := j')
            (pred := fun a ↦ ¬lt pivot a) H_q (by omega) (by omega))
      have H_q_arr_2 : RangeHas n (¬lt pivot arr_2[·]) (v_q + 1) right := by
        simpa only [arr_2] using
          (RangeHas.swap_after (n := n) (arr := arr_1) (i := v_p) (j := i')
            (pred := fun a ↦ ¬lt pivot a) H_q_arr_1 (by omega) (by omega))
      have H_q_tail_arr_3 : RangeHas n (¬lt pivot arr_3[·]) (v_q + 1) right := by
        simpa only [arr_3] using
          (RangeHas.swap_after (n := n) (arr := arr_2) (i := v_q) (j := j')
            (pred := fun a ↦ ¬lt pivot a) H_q_arr_2
            (Nat.lt_succ_self v_q) (by omega))
      have H_q_arr_3 : RangeHas n (¬lt pivot arr_3[·]) v_q right := by
        apply RangeHas.prepend (n := n) (a := v_q) (b := right) (ha := hq_n)
          (pred := fun x ↦ ¬lt pivot arr_3[x])
        · simpa only [arr_3, Fin.getElem_fin, Vector.getElem_swap_left] using h2
        · exact H_q_tail_arr_3
      dsimp only [arr_1, arr_2] at h1 h2
      unfold classic.loop
      simp only [x1, x2, dif_pos h_iltj, dif_neg h1, dif_neg h2]
      apply ih (by omega) H_left_arr_3
      · simpa only [show j' - 1 + 1 = j' by omega] using H_right_arr_3
      · exact H_p_arr_3
      · simpa only [hqsimp] using H_q_arr_3
  | case5 v_arr v_i v_j v_p v_q hpi hqr hli hij hjr hjq halgep haqltp
      j' isLtj' left2 hjpiv1 x1 hjpiv i' isLti' left1 left_ hapiv1 x2 hapiv
      h1 hp h2 arr'' j'' hj'' h_p arr''' i'' hi'' h_q =>
      have H_left_scan : RangeHas n (¬lt pivot v_arr[·]) left i' := by
        have hs := bentleyMcIlroy.classic.while_i'_extends_left
          (left := left) (right := v_q + 1) (start := left)
          (arr := v_arr) (i := v_i) (j := j') (ival := v_i)
          (hr := by omega) (hjr := by omega) (hii := Nat.le_refl _)
          (hxi := by omega) (harltp := haqltp) H_left
        simpa only [x2] using hs
      have H_right_scan :
          RangeHas n (¬lt v_arr[·] pivot) (j' + 1) (right + 1) := by
        have hs := bentleyMcIlroy.classic.while_j'_extends_right
          (left := v_p - 1) (right := right) (top := right + 1)
          (arr := v_arr) (i := v_i) (j := v_j) (jval := v_j)
          (hr := hr) (hl := by omega) (hjr := hjr) (hli := by omega)
          (hxj := by omega) (hjj := Nat.le_refl _) (halgep := halgep) H_right
        simpa only [x1] using hs
      unfold classic.loop
      simp only [x1, x2, h_p, h_q, dif_neg h1, dif_pos h2]
      have hj'_lower := classic.loop.while_j'_lower_bound
        (left := v_p - 1) (right := right) (hr := hr) (pivot := pivot)
        (arr := v_arr) (i := v_i) (j := v_j) (hjr := hjr) (hli := by omega)
        (jval := v_j) (hxj := by omega) (hjj := Nat.le_refl _) (halgep := halgep)
      simp only [x1] at hj'_lower
      have hfinish := move_pivots_back.sorted
        (hr := hr) (arr := v_arr) (pivot := pivot) (i := i') (j := j')
        (p := v_p) (q := v_q) (hjr := by omega) (hli := by omega)
        (hji := h2) (hpj := by omega) (hlp := hlp)
        (hiq := left_) (hqr := hqr) (hlo := by omega) (hhi := by omega)
        H_left_scan H_right_scan H_p H_q
      simpa only [h_p, h_q] using hfinish
  | case6 v_arr v_i v_j v_p v_q hpi hqr hli hij hjr hjq halgep haqltp
      j' isLtj' left2 hjpiv1 x1 hjpiv i' isLti' left1 left_ hapiv1 x2 hapiv
      h1 hp h2 arr'' j'' hj'' h_p arr''' i'' hi'' h_q =>
      have H_left_scan : RangeHas n (¬lt pivot v_arr[·]) left i' := by
        have hs := bentleyMcIlroy.classic.while_i'_extends_left
          (left := left) (right := v_q + 1) (start := left)
          (arr := v_arr) (i := v_i) (j := j') (ival := v_i)
          (hr := by omega) (hjr := by omega) (hii := Nat.le_refl _)
          (hxi := by omega) (harltp := haqltp) H_left
        simpa only [x2] using hs
      have H_right_scan :
          RangeHas n (¬lt v_arr[·] pivot) (j' + 1) (right + 1) := by
        have hs := bentleyMcIlroy.classic.while_j'_extends_right
          (left := v_p - 1) (right := right) (top := right + 1)
          (arr := v_arr) (i := v_i) (j := v_j) (jval := v_j)
          (hr := hr) (hl := by omega) (hjr := hjr) (hli := by omega)
          (hxj := by omega) (hjj := Nat.le_refl _) (halgep := halgep) H_right
        simpa only [x1] using hs
      have H_left' : RangeHas n (¬lt pivot v_arr[·]) left (i' + 1) := by
        apply RangeHas.append (n := n) (a := left) (b := i') (hb := isLti')
          (pred := fun x ↦ ¬lt pivot v_arr[x])
        · simpa only [show i' = j' by omega, Fin.getElem_fin] using hjpiv
        · exact H_left_scan
      have H_right' :
          RangeHas n (¬lt v_arr[·] pivot) (j' - 1 + 1) (right + 1) := by
        have hjpred : j' - 1 + 1 = j' := by omega
        rw [hjpred]
        apply RangeHas.prepend (n := n) (a := j') (b := right + 1) (ha := isLtj')
          (pred := fun x ↦ ¬lt v_arr[x] pivot)
        · simpa only [show j' = i' by omega, Fin.getElem_fin] using hapiv
        · exact H_right_scan
      unfold classic.loop
      simp only [x1, x2, h_p, h_q, dif_neg h1, dif_neg h2]
      have hfinish := move_pivots_back.sorted
        (hr := hr) (arr := v_arr) (pivot := pivot) (i := i' + 1) (j := j' - 1)
        (p := v_p) (q := v_q) (hjr := by omega) (hli := by omega)
        (hji := by omega) (hpj := by omega) (hlp := hlp)
        (hiq := by omega) (hqr := hqr) (hlo := by omega) (hhi := by omega)
        H_left' H_right' H_p H_q
      simpa only [h_p, h_q] using hfinish

theorem Partition.bentleyMcIlroy.classic.sorted [Ord α] [Std.TransOrd α] (arr : Vector α n) (left : Nat) (right : Nat) (hlr : left < right) (hr : right < n) :
    ∃ pivot, IsPartitioned left right pivot (Partition.bentleyMcIlroy.classic arr left right hlr hr).val := by
  let mid := left + ((right - left) / 2)
  have hlm : left ≤ mid := by omega
  have hmr : mid ≤ right := by
    have hdiv : (right - left) / 2 ≤ right - left := Nat.div_le_self _ _
    omega
  have hm : mid < n := Nat.lt_of_le_of_lt hmr hr
  let arr_ := arr
    |> (maybeSwap · ⟨left, by omega⟩ ⟨mid, by omega⟩)
    |> (maybeSwap · ⟨left, by omega⟩ ⟨right, by omega⟩)
    |> (maybeSwap · ⟨mid, by omega⟩ ⟨right, by omega⟩)
  let pivot := arr_[mid]
  have hmedian : ¬lt pivot arr_[left] ∧ ¬lt arr_[right] pivot :=
    median_of_three_sorted hlm hmr hr
  have H_left : RangeHas n (¬lt pivot arr_[·]) left (left + 1) := by
    intro x hx1 hx2
    have hxle : x.val ≤ left := Nat.le_of_lt_succ hx2
    have hx : x = (⟨left, by omega⟩ : Fin n) :=
      Fin.ext (Nat.le_antisymm hxle hx1)
    simpa only [hx, Fin.getElem_fin] using hmedian.1
  have H_right :
      RangeHas n (¬lt arr_[·] pivot) (right - 1 + 1) (right + 1) := by
    rw [show right - 1 + 1 = right by omega]
    intro x hx1 hx2
    have hxle : x.val ≤ right := Nat.le_of_lt_succ hx2
    have hx : x = (⟨right, hr⟩ : Fin n) :=
      Fin.ext (Nat.le_antisymm hxle hx1)
    simpa only [hx, Fin.getElem_fin] using hmedian.2
  have H_p : RangeHas n (¬lt arr_[·] pivot) (left + 1) (left + 1) :=
    RangeHas.refl _
  have H_q : RangeHas n (¬lt pivot arr_[·]) (right - 1 + 1) right := by
    simpa only [show right - 1 + 1 = right by omega] using
      (RangeHas.refl right : RangeHas n (¬lt pivot arr_[·]) right right)
  have halgep : ¬lt pivot arr_[left + 1 - 1] := by
    simpa only [show left + 1 - 1 = left by omega] using hmedian.1
  have haqltp : ¬lt arr_[right - 1 + 1] pivot := by
    simpa only [show right - 1 + 1 = right by omega] using hmedian.2
  have hloop := classic.loop.sorted
    (arr := arr_) (pivot := pivot) (hr := hr) (hl := by omega)
    (i := left + 1) (j := right - 1) (p := left + 1) (q := right - 1)
    (hli := by omega) (hij := by omega) (hjr := by omega)
    (hpi := Nat.le_refl _) (hqr := by omega) (hjq := Nat.le_refl _)
    (halgep := halgep) (haqltp := haqltp) (hlp := Nat.le_refl _)
    H_left H_right H_p H_q
  refine ⟨pivot, ?_⟩
  simpa only [classic, mid, arr_, pivot] using hloop


set_option maxHeartbeats 800000 in
theorem Partition.bentleyMcIlroy.eager.loop.sorted [Ord α] [Std.TransOrd α]
    {left right : Nat} {hlr : left < right} {hr : right < n} {pivot : α}
    {arr : Vector α n} {i j p q : Nat} {hpi : p ≤ i} {hqr : q < right}
    {hli : left < i} {hij : i ≤ j + 1} {hjr : j < right} {hjq : j ≤ q}
    (hlp : left + 1 ≤ p)
    (H_left : RangeHas n (¬lt pivot arr[·]) left i)
    (H_right : RangeHas n (¬lt arr[·] pivot) (j + 1) (right + 1))
    (H_p : RangeHas n (¬lt arr[·] pivot) (left + 1) p)
    (H_q : RangeHas n (¬lt pivot arr[·]) (q + 1) right) :
    IsPartitioned left right pivot (Partition.bentleyMcIlroy.eager.loop left right hlr hr pivot arr i j p q hli hij hjr hpi hqr hjq).val := by
  have lt_asymm : ∀ {x y : α}, lt x y → ¬lt y x := by grind
  induction arr, i, j, p, q, hli, hij, hjr, hpi, hqr, hjq using
      eager.loop.induct left right hlr hr pivot with
  | case1 v_arr v_i v_j v_p v_q hli hij hjr hpi hqr hjq hp h
      arr'' j'' hi''r x1 arr''' i'' hli'' x2 =>
      rw [eager.loop]
      simp only []
      repeat (split <;> try contradiction)
      simp only [*]
      have hfinish := move_pivots_back.sorted
        (hr := hr) (arr := v_arr) (pivot := pivot) (i := v_i) (j := v_j)
        (p := v_p) (q := v_q) (hjr := hjr) (hli := hli)
        (hji := h) (hpj := by omega) (hlp := hlp)
        (hiq := by omega) (hqr := hqr) (hlo := by omega) (hhi := by omega)
        H_left H_right H_p H_q
      simpa only [x1, x2] using hfinish
  | case2 v_arr v_i v_j v_p v_q hli hij hjr hpi hqr hjq hp hji hi ih =>
      rw [eager.loop]
      simp only []
      repeat (split <;> try contradiction)
      apply ih hlp
      · have hi_n : v_i < n := by omega
        apply RangeHas.append (n := n) (a := left) (b := v_i) (hb := hi_n)
          (pred := fun x ↦ ¬lt pivot v_arr[x])
        · simpa only [Fin.getElem_fin] using lt_asymm hi
        · exact H_left
      · exact H_right
      · exact H_p
      · exact H_q
  | case3 v_arr v_i v_j v_p v_q hli hij hjr hpi hqr hjq hp hji hi hj ih =>
      rw [eager.loop]
      simp only []
      repeat (split <;> try contradiction)
      apply ih hlp H_left
      · have hj_n : v_j < n := by omega
        have hjpred : v_j - 1 + 1 = v_j := by omega
        rw [hjpred]
        apply RangeHas.prepend (n := n) (a := v_j) (b := right + 1) (ha := hj_n)
          (pred := fun x ↦ ¬lt v_arr[x] pivot)
        · simpa only [Fin.getElem_fin] using lt_asymm hj
        · exact H_right
      · exact H_p
      · exact H_q
  | case4 v_arr v_i v_j v_p v_q hli hij hjr hpi hqr hjq hp hji hi hj hij'
      arr' hi' hj' ih =>
      rw [eager.loop]
      simp only []
      repeat (split <;> try contradiction)
      have H_left_arr' :
          RangeHas n (¬lt pivot arr'[·]) left v_i := by
        simpa only [arr'] using
          (RangeHas.swap_before (n := n) (arr := v_arr) (i := v_i) (j := v_j)
            (pred := fun a ↦ ¬lt pivot a) H_left (Nat.le_refl v_i) (by omega))
      have H_right_arr' :
          RangeHas n (¬lt arr'[·] pivot) (v_j + 1) (right + 1) := by
        simpa only [arr'] using
          (RangeHas.swap_after (n := n) (arr := v_arr) (i := v_i) (j := v_j)
            (pred := fun a ↦ ¬lt a pivot) H_right (by omega) (Nat.lt_succ_self v_j))
      have H_p_arr' : RangeHas n (¬lt arr'[·] pivot) (left + 1) v_p := by
        simpa only [arr'] using
          (RangeHas.swap_before (n := n) (arr := v_arr) (i := v_i) (j := v_j)
            (pred := fun a ↦ ¬lt a pivot) H_p hpi (by omega))
      have H_q_arr' : RangeHas n (¬lt pivot arr'[·]) (v_q + 1) right := by
        simpa only [arr'] using
          (RangeHas.swap_after (n := n) (arr := v_arr) (i := v_i) (j := v_j)
            (pred := fun a ↦ ¬lt pivot a) H_q (by omega) (by omega))
      apply ih hlp
      · have hi_n : v_i < n := by omega
        apply RangeHas.append (n := n) (a := left) (b := v_i) (hb := hi_n)
          (pred := fun x ↦ ¬lt pivot arr'[x])
        · simpa only [Fin.getElem_fin] using lt_asymm hi'
        · exact H_left_arr'
      · have hj_n : v_j < n := by omega
        have hjpred : v_j - 1 + 1 = v_j := by omega
        rw [hjpred]
        apply RangeHas.prepend (n := n) (a := v_j) (b := right + 1) (ha := hj_n)
          (pred := fun x ↦ ¬lt arr'[x] pivot)
        · simpa only [Fin.getElem_fin] using lt_asymm hj'
        · exact H_right_arr'
      · exact H_p_arr'
      · exact H_q_arr'
  | case5 v_arr v_i v_j v_p v_q hli hij hjr hpi hqr hjq hp h5 h4 h3 h2
      arr' h1 h arr'' ih =>
      rw [eager.loop]
      simp only []
      repeat (split <;> try contradiction)
      have hi_n : v_i < n := by omega
      have hj_n : v_j < n := by omega
      have hq_n : v_q < n := by omega
      have hjpred : v_j - 1 + 1 = v_j := by omega
      have hqpred : v_q - 1 + 1 = v_q := by omega
      have H_left_arr' : RangeHas n (¬lt pivot arr'[·]) left v_i := by
        simpa only [arr'] using
          (RangeHas.swap_before (n := n) (arr := v_arr) (i := v_i) (j := v_j)
            (pred := fun a ↦ ¬lt pivot a) H_left (Nat.le_refl v_i) (by omega))
      have H_left_arr'_plus :
          RangeHas n (¬lt pivot arr'[·]) left (v_i + 1) := by
        apply RangeHas.append (n := n) (a := left) (b := v_i) (hb := hi_n)
          (pred := fun x ↦ ¬lt pivot arr'[x])
        · simpa only [Fin.getElem_fin] using lt_asymm h1
        · exact H_left_arr'
      have H_left_arr'' :
          RangeHas n (¬lt pivot arr''[·]) left (v_i + 1) := by
        simpa only [arr''] using
          (RangeHas.swap_before (n := n) (arr := arr') (i := v_q) (j := v_j)
            (pred := fun a ↦ ¬lt pivot a) H_left_arr'_plus (by omega) (by omega))
      have H_p_arr' : RangeHas n (¬lt arr'[·] pivot) (left + 1) v_p := by
        simpa only [arr'] using
          (RangeHas.swap_before (n := n) (arr := v_arr) (i := v_i) (j := v_j)
            (pred := fun a ↦ ¬lt a pivot) H_p hpi (by omega))
      have H_p_arr'' : RangeHas n (¬lt arr''[·] pivot) (left + 1) v_p := by
        simpa only [arr''] using
          (RangeHas.swap_before (n := n) (arr := arr') (i := v_q) (j := v_j)
            (pred := fun a ↦ ¬lt a pivot) H_p_arr' (by omega) (by omega))
      have H_right_tail_arr' :
          RangeHas n (¬lt arr'[·] pivot) (v_j + 1) (right + 1) := by
        simpa only [arr'] using
          (RangeHas.swap_after (n := n) (arr := v_arr) (i := v_i) (j := v_j)
            (pred := fun a ↦ ¬lt a pivot) H_right (by omega) (Nat.lt_succ_self v_j))
      have H_j_high_arr' : ¬lt arr'[(⟨v_j, hj_n⟩ : Fin n)] pivot := by
        simpa only [arr', Fin.getElem_fin, Vector.getElem_swap_right] using h4
      have H_right_arr' : RangeHas n (¬lt arr'[·] pivot) v_j (right + 1) := by
        apply RangeHas.prepend (n := n) (a := v_j) (b := right + 1) (ha := hj_n)
          (pred := fun x ↦ ¬lt arr'[x] pivot)
        · exact H_j_high_arr'
        · exact H_right_tail_arr'
      have H_q_high_arr' : ¬lt arr'[(⟨v_q, hq_n⟩ : Fin n)] pivot :=
        H_right_arr' ⟨v_q, hq_n⟩ (by omega) (Nat.lt_succ_of_lt hqr)
      have H_right_arr'' : RangeHas n (¬lt arr''[·] pivot) v_j (right + 1) := by
        simpa only [arr''] using
          (RangeHas.swap_of_pred (n := n) (arr := arr') (i := v_q) (j := v_j)
            (pred := fun a ↦ ¬lt a pivot) H_right_arr' H_q_high_arr' H_j_high_arr')
      have H_q_tail_arr' : RangeHas n (¬lt pivot arr'[·]) (v_q + 1) right := by
        simpa only [arr'] using
          (RangeHas.swap_after (n := n) (arr := v_arr) (i := v_i) (j := v_j)
            (pred := fun a ↦ ¬lt pivot a) H_q (by omega) (by omega))
      have H_q_tail_arr'' : RangeHas n (¬lt pivot arr''[·]) (v_q + 1) right := by
        simpa only [arr''] using
          (RangeHas.swap_after (n := n) (arr := arr') (i := v_q) (j := v_j)
            (pred := fun a ↦ ¬lt pivot a) H_q_tail_arr'
            (Nat.lt_succ_self v_q) (by omega))
      have H_q_arr'' : RangeHas n (¬lt pivot arr''[·]) v_q right := by
        apply RangeHas.prepend (n := n) (a := v_q) (b := right) (ha := hq_n)
          (pred := fun x ↦ ¬lt pivot arr''[x])
        · simpa only [arr'', Fin.getElem_fin, Vector.getElem_swap_left] using h
        · exact H_q_tail_arr''
      apply ih hlp H_left_arr''
      · simpa only [hjpred] using H_right_arr''
      · exact H_p_arr''
      · simpa only [hqpred] using H_q_arr''
  | case6 v_arr v_i v_j v_p v_q hli hij hjr hpi hqr hjq hp h5 h4 h3 h2
      arr' h1 arr'' h ih =>
      rw [eager.loop]
      simp only []
      repeat (split <;> try contradiction)
      have hi_n : v_i < n := by omega
      have hj_n : v_j < n := by omega
      have H_left_arr' : RangeHas n (¬lt pivot arr'[·]) left v_i := by
        simpa only [arr'] using
          (RangeHas.swap_before (n := n) (arr := v_arr) (i := v_i) (j := v_j)
            (pred := fun a ↦ ¬lt pivot a) H_left (Nat.le_refl v_i) (by omega))
      have H_i_low_arr' : ¬lt pivot arr'[(⟨v_i, hi_n⟩ : Fin n)] := by
        simpa only [arr', Fin.getElem_fin, Vector.getElem_swap_left] using h3
      have H_left_arr'_plus :
          RangeHas n (¬lt pivot arr'[·]) left (v_i + 1) := by
        apply RangeHas.append (n := n) (a := left) (b := v_i) (hb := hi_n)
          (pred := fun x ↦ ¬lt pivot arr'[x])
        · exact H_i_low_arr'
        · exact H_left_arr'
      have H_p_low_arr' : ¬lt pivot arr'[(⟨v_p, hp⟩ : Fin n)] :=
        H_left_arr'_plus ⟨v_p, hp⟩
          (Nat.le_trans (Nat.le_succ left) hlp) (Nat.lt_succ_of_le hpi)
      have H_left_arr'' :
          RangeHas n (¬lt pivot arr''[·]) left (v_i + 1) := by
        simpa only [arr''] using
          (RangeHas.swap_of_pred (n := n) (arr := arr') (i := v_p) (j := v_i)
            (pred := fun a ↦ ¬lt pivot a) H_left_arr'_plus H_p_low_arr' H_i_low_arr')
      have H_p_arr' : RangeHas n (¬lt arr'[·] pivot) (left + 1) v_p := by
        simpa only [arr'] using
          (RangeHas.swap_before (n := n) (arr := v_arr) (i := v_i) (j := v_j)
            (pred := fun a ↦ ¬lt a pivot) H_p hpi (by omega))
      have H_p_before_arr'' : RangeHas n (¬lt arr''[·] pivot) (left + 1) v_p := by
        simpa only [arr''] using
          (RangeHas.swap_before (n := n) (arr := arr') (i := v_p) (j := v_i)
            (pred := fun a ↦ ¬lt a pivot) H_p_arr' (Nat.le_refl v_p) hpi)
      have H_p_arr'' : RangeHas n (¬lt arr''[·] pivot) (left + 1) (v_p + 1) := by
        apply RangeHas.append (n := n) (a := left + 1) (b := v_p) (hb := hp)
          (pred := fun x ↦ ¬lt arr''[x] pivot)
        · simpa only [arr'', Fin.getElem_fin, Vector.getElem_swap_left] using h1
        · exact H_p_before_arr''
      have H_right_arr' :
          RangeHas n (¬lt arr'[·] pivot) (v_j + 1) (right + 1) := by
        simpa only [arr'] using
          (RangeHas.swap_after (n := n) (arr := v_arr) (i := v_i) (j := v_j)
            (pred := fun a ↦ ¬lt a pivot) H_right (by omega) (Nat.lt_succ_self v_j))
      have H_right_tail_arr'' :
          RangeHas n (¬lt arr''[·] pivot) (v_j + 1) (right + 1) := by
        simpa only [arr''] using
          (RangeHas.swap_after (n := n) (arr := arr') (i := v_p) (j := v_i)
            (pred := fun a ↦ ¬lt a pivot) H_right_arr' (by omega) (by omega))
      have H_right_arr'' : RangeHas n (¬lt arr''[·] pivot) v_j (right + 1) := by
        apply RangeHas.prepend (n := n) (a := v_j) (b := right + 1) (ha := hj_n)
          (pred := fun x ↦ ¬lt arr''[x] pivot)
        · simpa only [Fin.getElem_fin] using lt_asymm h
        · exact H_right_tail_arr''
      have H_q_arr' : RangeHas n (¬lt pivot arr'[·]) (v_q + 1) right := by
        simpa only [arr'] using
          (RangeHas.swap_after (n := n) (arr := v_arr) (i := v_i) (j := v_j)
            (pred := fun a ↦ ¬lt pivot a) H_q (by omega) (by omega))
      have H_q_arr'' : RangeHas n (¬lt pivot arr''[·]) (v_q + 1) right := by
        simpa only [arr''] using
          (RangeHas.swap_after (n := n) (arr := arr') (i := v_p) (j := v_i)
            (pred := fun a ↦ ¬lt pivot a) H_q_arr' (by omega) (by omega))
      apply ih (by omega) H_left_arr''
      · simpa only [show v_j - 1 + 1 = v_j by omega] using H_right_arr''
      · exact H_p_arr''
      · exact H_q_arr''
  | case7 v_arr v_i v_j v_p v_q hli hij hjr hpi hqr hjq hp h5 h4 h3 h2
      arr' h1 arr'' h arr''' ih =>
      rw [eager.loop]
      simp only []
      repeat (split <;> try contradiction)
      have hi_n : v_i < n := by omega
      have hj_n : v_j < n := by omega
      have hq_n : v_q < n := by omega
      have H_left_arr' : RangeHas n (¬lt pivot arr'[·]) left v_i := by
        simpa only [arr'] using
          (RangeHas.swap_before (n := n) (arr := v_arr) (i := v_i) (j := v_j)
            (pred := fun a ↦ ¬lt pivot a) H_left (Nat.le_refl v_i) (by omega))
      have H_i_low_arr' : ¬lt pivot arr'[(⟨v_i, hi_n⟩ : Fin n)] := by
        simpa only [arr', Fin.getElem_fin, Vector.getElem_swap_left] using h3
      have H_left_arr'_plus :
          RangeHas n (¬lt pivot arr'[·]) left (v_i + 1) := by
        apply RangeHas.append (n := n) (a := left) (b := v_i) (hb := hi_n)
          (pred := fun x ↦ ¬lt pivot arr'[x])
        · exact H_i_low_arr'
        · exact H_left_arr'
      have H_p_low_arr' : ¬lt pivot arr'[(⟨v_p, hp⟩ : Fin n)] :=
        H_left_arr'_plus ⟨v_p, hp⟩
          (Nat.le_trans (Nat.le_succ left) hlp) (Nat.lt_succ_of_le hpi)
      have H_left_arr'' :
          RangeHas n (¬lt pivot arr''[·]) left (v_i + 1) := by
        simpa only [arr''] using
          (RangeHas.swap_of_pred (n := n) (arr := arr') (i := v_p) (j := v_i)
            (pred := fun a ↦ ¬lt pivot a) H_left_arr'_plus H_p_low_arr' H_i_low_arr')
      have H_left_arr''' :
          RangeHas n (¬lt pivot arr'''[·]) left (v_i + 1) := by
        simpa only [arr'''] using
          (RangeHas.swap_before (n := n) (arr := arr'') (i := v_q) (j := v_j)
            (pred := fun a ↦ ¬lt pivot a) H_left_arr'' (by omega) (by omega))
      have H_p_arr' : RangeHas n (¬lt arr'[·] pivot) (left + 1) v_p := by
        simpa only [arr'] using
          (RangeHas.swap_before (n := n) (arr := v_arr) (i := v_i) (j := v_j)
            (pred := fun a ↦ ¬lt a pivot) H_p hpi (by omega))
      have H_p_before_arr'' : RangeHas n (¬lt arr''[·] pivot) (left + 1) v_p := by
        simpa only [arr''] using
          (RangeHas.swap_before (n := n) (arr := arr') (i := v_p) (j := v_i)
            (pred := fun a ↦ ¬lt a pivot) H_p_arr' (Nat.le_refl v_p) hpi)
      have H_p_arr'' : RangeHas n (¬lt arr''[·] pivot) (left + 1) (v_p + 1) := by
        apply RangeHas.append (n := n) (a := left + 1) (b := v_p) (hb := hp)
          (pred := fun x ↦ ¬lt arr''[x] pivot)
        · simpa only [arr'', Fin.getElem_fin, Vector.getElem_swap_left] using h1
        · exact H_p_before_arr''
      have H_p_arr''' :
          RangeHas n (¬lt arr'''[·] pivot) (left + 1) (v_p + 1) := by
        simpa only [arr'''] using
          (RangeHas.swap_before (n := n) (arr := arr'') (i := v_q) (j := v_j)
            (pred := fun a ↦ ¬lt a pivot) H_p_arr'' (by omega) (by omega))
      have H_right_arr' :
          RangeHas n (¬lt arr'[·] pivot) (v_j + 1) (right + 1) := by
        simpa only [arr'] using
          (RangeHas.swap_after (n := n) (arr := v_arr) (i := v_i) (j := v_j)
            (pred := fun a ↦ ¬lt a pivot) H_right (by omega) (Nat.lt_succ_self v_j))
      have H_right_tail_arr'' :
          RangeHas n (¬lt arr''[·] pivot) (v_j + 1) (right + 1) := by
        simpa only [arr''] using
          (RangeHas.swap_after (n := n) (arr := arr') (i := v_p) (j := v_i)
            (pred := fun a ↦ ¬lt a pivot) H_right_arr' (by omega) (by omega))
      have H_j_high_arr'' : ¬lt arr''[(⟨v_j, hj_n⟩ : Fin n)] pivot := by
        simp only [arr'', Fin.getElem_fin,
          Vector.getElem_swap_of_ne (show v_j ≠ v_p by omega) (show v_j ≠ v_i by omega)]
        simpa only [arr', Vector.getElem_swap_right] using h4
      have H_right_arr'' : RangeHas n (¬lt arr''[·] pivot) v_j (right + 1) := by
        apply RangeHas.prepend (n := n) (a := v_j) (b := right + 1) (ha := hj_n)
          (pred := fun x ↦ ¬lt arr''[x] pivot)
        · exact H_j_high_arr''
        · exact H_right_tail_arr''
      have H_q_high_arr'' : ¬lt arr''[(⟨v_q, hq_n⟩ : Fin n)] pivot :=
        H_right_arr'' ⟨v_q, hq_n⟩ (by omega) (Nat.lt_succ_of_lt hqr)
      have H_right_arr''' : RangeHas n (¬lt arr'''[·] pivot) v_j (right + 1) := by
        simpa only [arr'''] using
          (RangeHas.swap_of_pred (n := n) (arr := arr'') (i := v_q) (j := v_j)
            (pred := fun a ↦ ¬lt a pivot) H_right_arr'' H_q_high_arr'' H_j_high_arr'')
      have H_q_arr' : RangeHas n (¬lt pivot arr'[·]) (v_q + 1) right := by
        simpa only [arr'] using
          (RangeHas.swap_after (n := n) (arr := v_arr) (i := v_i) (j := v_j)
            (pred := fun a ↦ ¬lt pivot a) H_q (by omega) (by omega))
      have H_q_arr'' : RangeHas n (¬lt pivot arr''[·]) (v_q + 1) right := by
        simpa only [arr''] using
          (RangeHas.swap_after (n := n) (arr := arr') (i := v_p) (j := v_i)
            (pred := fun a ↦ ¬lt pivot a) H_q_arr' (by omega) (by omega))
      have H_q_tail_arr''' : RangeHas n (¬lt pivot arr'''[·]) (v_q + 1) right := by
        simpa only [arr'''] using
          (RangeHas.swap_after (n := n) (arr := arr'') (i := v_q) (j := v_j)
            (pred := fun a ↦ ¬lt pivot a) H_q_arr''
            (Nat.lt_succ_self v_q) (by omega))
      have H_q_arr''' : RangeHas n (¬lt pivot arr'''[·]) v_q right := by
        apply RangeHas.prepend (n := n) (a := v_q) (b := right) (ha := hq_n)
          (pred := fun x ↦ ¬lt pivot arr'''[x])
        · simpa only [arr''', Fin.getElem_fin, Vector.getElem_swap_left] using h
        · exact H_q_tail_arr'''
      apply ih (by omega) H_left_arr'''
      · simpa only [show v_j - 1 + 1 = v_j by omega] using H_right_arr'''
      · exact H_p_arr'''
      · simpa only [show v_q - 1 + 1 = v_q by omega] using H_q_arr'''
  | case8 v_arr v_i v_j v_p v_q hli hij hjr hpi hqr hjq hp hji hi hj hij'
      arr'' j'' hi''r x1 arr''' i'' hli'' x2 =>
      rw [eager.loop]
      simp only []
      repeat (split <;> try contradiction)
      simp only [*]
      have H_left' : RangeHas n (¬lt pivot v_arr[·]) left (v_i + 1) := by
        have hi_n : v_i < n := by omega
        apply RangeHas.append (n := n) (a := left) (b := v_i) (hb := hi_n)
          (pred := fun x ↦ ¬lt pivot v_arr[x])
        · simpa only [show v_i = v_j by omega, Fin.getElem_fin] using hj
        · exact H_left
      have H_right' :
          RangeHas n (¬lt v_arr[·] pivot) (v_j - 1 + 1) (right + 1) := by
        have hj_n : v_j < n := by omega
        have hjpred : v_j - 1 + 1 = v_j := by omega
        rw [hjpred]
        apply RangeHas.prepend (n := n) (a := v_j) (b := right + 1) (ha := hj_n)
          (pred := fun x ↦ ¬lt v_arr[x] pivot)
        · simpa only [show v_j = v_i by omega, Fin.getElem_fin] using hi
        · exact H_right
      have hfinish := move_pivots_back.sorted
        (hr := hr) (arr := v_arr) (pivot := pivot) (i := v_i + 1) (j := v_j - 1)
        (p := v_p) (q := v_q) (hjr := by omega) (hli := by omega)
        (hji := by omega) (hpj := by omega) (hlp := hlp)
        (hiq := by omega) (hqr := hqr) (hlo := by omega) (hhi := by omega)
        H_left' H_right' H_p H_q
      simpa only [x1, x2] using hfinish

theorem Partition.bentleyMcIlroy.eager.sorted [Ord α] [Std.TransOrd α] (arr : Vector α n) (left : Nat) (right : Nat) (hlr : left < right) (hr : right < n) :
    ∃ pivot, IsPartitioned left right pivot (Partition.bentleyMcIlroy.eager arr left right hlr hr).val := by
  let mid := left + ((right - left) / 2)
  have hlm : left ≤ mid := by omega
  have hmr : mid ≤ right := by
    have hdiv : (right - left) / 2 ≤ right - left := Nat.div_le_self _ _
    omega
  have hm : mid < n := Nat.lt_of_le_of_lt hmr hr
  let arr_ := arr
    |> (maybeSwap · ⟨left, by omega⟩ ⟨mid, by omega⟩)
    |> (maybeSwap · ⟨left, by omega⟩ ⟨right, by omega⟩)
    |> (maybeSwap · ⟨mid, by omega⟩ ⟨right, by omega⟩)
  let pivot := arr_[mid]
  have hmedian : ¬lt pivot arr_[left] ∧ ¬lt arr_[right] pivot :=
    median_of_three_sorted hlm hmr hr
  have H_left : RangeHas n (¬lt pivot arr_[·]) left (left + 1) := by
    intro x hx1 hx2
    have hxle : x.val ≤ left := Nat.le_of_lt_succ hx2
    have hx : x = (⟨left, by omega⟩ : Fin n) :=
      Fin.ext (Nat.le_antisymm hxle hx1)
    simpa only [hx, Fin.getElem_fin] using hmedian.1
  have H_right :
      RangeHas n (¬lt arr_[·] pivot) (right - 1 + 1) (right + 1) := by
    rw [show right - 1 + 1 = right by omega]
    intro x hx1 hx2
    have hxle : x.val ≤ right := Nat.le_of_lt_succ hx2
    have hx : x = (⟨right, hr⟩ : Fin n) :=
      Fin.ext (Nat.le_antisymm hxle hx1)
    simpa only [hx, Fin.getElem_fin] using hmedian.2
  have H_p : RangeHas n (¬lt arr_[·] pivot) (left + 1) (left + 1) :=
    RangeHas.refl _
  have H_q : RangeHas n (¬lt pivot arr_[·]) (right - 1 + 1) right := by
    simpa only [show right - 1 + 1 = right by omega] using
      (RangeHas.refl right : RangeHas n (¬lt pivot arr_[·]) right right)
  have hloop := eager.loop.sorted
    (arr := arr_) (pivot := pivot) (hlr := hlr) (hr := hr)
    (i := left + 1) (j := right - 1)
    (p := left + 1) (q := right - 1) (hlp := Nat.le_refl _)
    (hli := by omega) (hij := by omega) (hjr := by omega)
    (hpi := Nat.le_refl _) (hqr := by omega) (hjq := Nat.le_refl _)
    H_left H_right H_p H_q
  refine ⟨pivot, ?_⟩
  simpa only [eager, mid, arr_, pivot] using hloop


theorem Partition.bentleyMcIlroy.sorted [Ord α] [Std.TransOrd α]  (arr : Vector α n) (left : Nat) (right : Nat) (hlr : left < right) (hr : right < n) :
    ∃ pivot, IsPartitioned left right pivot (Partition.bentleyMcIlroy arr left right hlr hr).val := by
  unfold Partition.bentleyMcIlroy; simp [*]; split
  · apply Partition.bentleyMcIlroy.classic.sorted <;> grind
  · apply Partition.bentleyMcIlroy.eager.sorted <;> grind

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
  induction as, left, right, hsize' using qsort_bentleyMcIlroy.sort.induct with
  | case1 as left right hsize' hlr as' j' i' hli' hjr' heq as'' ih1 ih2 =>
    unfold sort; simp only [↓reduceDIte, hlr, heq]

    intro i j hli hij hjr; exact

    have hji' : j' < i' := by
      have := Partition.bentleyMcIlroy.partition_bounds (arr := as) (left := left) (right := right) (hlr := hlr) (hr := by omega)
      have heq' : (Partition.bentleyMcIlroy as left right hlr (by omega)).val = ⟨as', j', i'⟩ := by exact congrArg Subtype.val heq
      rw [heq'] at this
      exact this
    let as''' := sort as'' i' right (by omega)

    if hhi : i' ≤ i.val then by
      apply ih2 <;> assumption
    else if hhj : j.val ≤ j' then by
      rw [qsort_bentleyMcIlroy.sort.permStabilizing.2.left j (by omega), qsort_bentleyMcIlroy.sort.permStabilizing.2.left i (by omega)]
      apply ih1 <;> assumption
    else by
      replace hhi : i.val < i' := by omega
      replace hhj : j' < j.val := by omega

      have ⟨pivot, ih0⟩ := Partition.bentleyMcIlroy.sorted as left right hlr (by omega)
      replace ih0 :
          (∀ (i : Fin n), left ≤ i → i < i' → ¬lt pivot as'[i]) ∧
          (∀ (j : Fin n), j' + 1 ≤ j → j < right + 1 → ¬lt as'[j] pivot) := by
        unfold Partition.IsPartitioned at ih0;
        have heq' : (Partition.bentleyMcIlroy as left right hlr (by omega)).val = ⟨as', j', i'⟩ := by exact congrArg Subtype.val heq
        rwa [heq'] at ih0

      have hhh1 : ¬lt pivot as'''[i] :=
        suffices ¬lt pivot as''[i] by rwa [qsort_bentleyMcIlroy.sort.permStabilizing.2.left i (by omega)]
        if _ : i.val ≤ j' then by
          apply Vector.PermStabilizing'.invariance (motive := (¬lt pivot ·)) (left := left) (hi := j' + 1) (hperm := qsort_bentleyMcIlroy.sort.permStabilizing) (hr' := by omega) (h := ?_ )
          any_goals omega
          · intro i_ _ _
            apply ih0.left i_ <;> omega
        else by
          rw [qsort_bentleyMcIlroy.sort.permStabilizing.2.right _ (by omega)]
          apply ih0.left i
          all_goals omega

      have hhh2 : ¬lt as'''[j] pivot :=
        if _ : i' ≤ j.val then by
          apply Vector.PermStabilizing'.invariance (motive := (¬lt · pivot)) (left := i') (hi := right + 1) (hperm := qsort_bentleyMcIlroy.sort.permStabilizing) (hr' := by omega) (h := ?_)
          any_goals omega
          · intro j_ _ _
            rw [qsort_bentleyMcIlroy.sort.permStabilizing.2.right j_ (by omega)]
            apply ih0.right j_ <;> omega
        else by
          rw [qsort_bentleyMcIlroy.sort.permStabilizing.2.left _ (by omega), qsort_bentleyMcIlroy.sort.permStabilizing.2.right _ (by omega)]
          apply ih0.right j
          all_goals omega

      exact le_trans' hhh1 hhh2
  | case2 as left right hsize' hlr =>
    unfold sort; simp only [↓reduceDIte, hlr]
    intro i j hli hij hjr
    have : left = right := by omega
    omega

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
  induction as, left, right, hsize' using qsort_bentleyMcIlroy_strict.sort.induct with
  | case1 as left right hsize' hlr as' j' i' hli' hjr' heq as'' ih1 ih2 =>
    unfold sort; simp only [↓reduceDIte, hlr, heq]

    intro i j hli hij hjr; exact

    have hji' : j' < i' := by
      have := Partition.bentleyMcIlroy.classic.partition_bounds (arr := as) (left := left) (right := right) (hlr := hlr) (hr := by omega)
      have heq' : (Partition.bentleyMcIlroy.classic as left right hlr (by omega)).val = ⟨as', j', i'⟩ := by exact congrArg Subtype.val heq
      rw [heq'] at this
      exact this
    let as''' := sort as'' i' right (by omega)

    if hhi : i' ≤ i.val then by
      apply ih2 <;> assumption
    else if hhj : j.val ≤ j' then by
      rw [qsort_bentleyMcIlroy_strict.sort.permStabilizing.2.left j (by omega), qsort_bentleyMcIlroy_strict.sort.permStabilizing.2.left i (by omega)]
      apply ih1 <;> assumption
    else by
      replace hhi : i.val < i' := by omega
      replace hhj : j' < j.val := by omega

      have ⟨pivot, ih0⟩ := Partition.bentleyMcIlroy.classic.sorted as left right hlr (by omega)
      replace ih0 :
          (∀ (i : Fin n), left ≤ i → i < i' → ¬lt pivot as'[i]) ∧
          (∀ (j : Fin n), j' + 1 ≤ j → j < right + 1 → ¬lt as'[j] pivot) := by
        unfold Partition.IsPartitioned at ih0;
        have heq' : (Partition.bentleyMcIlroy.classic as left right hlr (by omega)).val = ⟨as', j', i'⟩ := by exact congrArg Subtype.val heq
        rwa [heq'] at ih0

      have hhh1 : ¬lt pivot as'''[i] :=
        suffices ¬lt pivot as''[i] by rwa [qsort_bentleyMcIlroy_strict.sort.permStabilizing.2.left i (by omega)]
        if _ : i.val ≤ j' then by
          apply Vector.PermStabilizing'.invariance (motive := (¬lt pivot ·)) (left := left) (hi := j' + 1) (hperm := qsort_bentleyMcIlroy_strict.sort.permStabilizing) (hr' := by omega) (h := ?_ )
          any_goals omega
          · intro i_ _ _
            apply ih0.left i_ <;> omega
        else by
          rw [qsort_bentleyMcIlroy_strict.sort.permStabilizing.2.right _ (by omega)]
          apply ih0.left i
          all_goals omega

      have hhh2 : ¬lt as'''[j] pivot :=
        if _ : i' ≤ j.val then by
          apply Vector.PermStabilizing'.invariance (motive := (¬lt · pivot)) (left := i') (hi := right + 1) (hperm := qsort_bentleyMcIlroy_strict.sort.permStabilizing) (hr' := by omega) (h := ?_)
          any_goals omega
          · intro j_ _ _
            rw [qsort_bentleyMcIlroy_strict.sort.permStabilizing.2.right j_ (by omega)]
            apply ih0.right j_ <;> omega
        else by
          rw [qsort_bentleyMcIlroy_strict.sort.permStabilizing.2.left _ (by omega), qsort_bentleyMcIlroy_strict.sort.permStabilizing.2.right _ (by omega)]
          apply ih0.right j
          all_goals omega

      exact le_trans' hhh1 hhh2
  | case2 as left right hsize' hlr =>
    unfold sort; simp only [↓reduceDIte, hlr]
    intro i j hli hij hjr
    have : left = right := by omega
    omega

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
