/-
Copyright (c) 2024 Mombo Solutions, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Chisomo Makombo Sakala
-/

import SwapsPerm
import Quicksort.Order.Defs


section utils
theorem mtp {p q : Prop} (hpq: p ∨ q)(hnp: ¬ p):  q :=  by cases hpq; contradiction; assumption

theorem Nat.pred_def {n m:Nat} : n < m → n ≤ m.pred := by
  intro h
  apply Nat.le_of_succ_le_succ; exact
  if _ : m = 0 then
    have : m.pred < m := Nat.pred_lt' h
    by simp_all
  else
    Nat.succ_pred ‹m ≠ 0› |>.symm ▸ h


theorem Nat.sub_lt_sub {n m k : Nat} (h1 : k < m) (h2 : n < m) : n - k <  m - k :=
  if h0 : k ≤ n then
    -- Nat.sub_lt_sub' h0 h2
    match k with
    | 0 => by simp_all
    | k + 1 =>
      suffices n - k - 1 < m - k - 1 from (Nat.sub_add_eq ..) ▸ this

      have : n - k + k = n := Nat.sub_add_cancel (Nat.le_of_lt h0)
      have : n - k + k < m := this.symm ▸ h2
      have h2' : n - k < m - k := Nat.lt_sub_of_add_lt this

      have  : 1 + k ≤ n := k.add_comm 1 ▸ h0
      have h1': 1 ≤ n - k := Nat.le_sub_of_add_le this

      pred_lt_pred' h1' h2'
  else
    have  : n ≤ k := Nat.le_of_lt (Nat.gt_of_not_le h0)

    have h0' : n - k = 0 := Nat.sub_eq_zero_of_le this
    have h1' : 0 < m - k := Nat.zero_lt_sub_of_lt h1
    h0'.symm ▸ h1'

  where pred_lt_pred' : ∀ {n m}, 1 ≤ n → n < m →  n - 1 <  m - 1 | _+1, _+1, _, h => Nat.lt_of_succ_lt_succ h

theorem Nat.avg_bounds {a b c : Nat} (h1 : a ≤ b) (h2 : c = a + ((b-a)/2)) : a ≤ c ∧ c ≤ b :=
  suffices a ≤ (a + ((b-a)/2)) ∧ (a + ((b-a)/2)) ≤ b from h2.symm ▸ this

  have : (a + ((b-a)/2)) ≤ b :=
    have : ((b - a)/2) ≤ b-a := Nat.div_le_self (b - a) 2
    have : a + ((b - a)/2) ≤ a + (b - a) := Nat.add_le_add_left this a
    Trans.trans this (Nat.add_sub_of_le h1)

  ⟨Nat.le_add_right .., this⟩

@[simp] theorem Fin.le_of_val_le {n} : ∀ {i j : Fin n}, i.val ≤ j.val → i ≤ j
  | ⟨_, _⟩, ⟨_, _⟩, h => h

@[simp] theorem Nat.lt_of_le_and_neq {n m: Nat} (h1: n ≤ m) (h2: n ≠ m): n < m :=
  mtp (Nat.eq_or_lt_of_le h1) h2


theorem Nat.lt_asymm' {n m : Nat} : ¬(n < m ∧ m < n) := show ¬(n.succ ≤ m ∧ m.succ ≤ n) from fun ⟨h1, h2⟩ =>
  have : m < m.succ := Nat.lt_succ_self m
  have := Trans.trans (Trans.trans h1 this) h2
  have := Nat.le_of_lt this
  (show ¬(n ≤ n) from Nat.not_le_of_gt this) (show n ≤ n from Nat.le_of_lt this)


theorem Nat.not_le_and_gt {n m : Nat} : ¬(n ≤ m ∧ m < n) := fun ⟨hle, hlt⟩ =>
  have hne : m ≠ n := Nat.ne_of_lt hlt
  have hle : n < m := Nat.lt_of_le_and_neq hle hne.symm
  Nat.lt_asymm' ⟨hle, hlt⟩

theorem nat_mix {ival i'val jval j'val : Nat } (h1 : ival ≤ i'val) (h2 : j'val ≤ jval) (h0 : i'val < j'val) :  j'val.pred.succ - i'val.succ < jval.succ - ival :=
  have hj : j'val < jval.succ := Nat.lt_succ_of_le h2
  have hijs : ival ≤ jval.succ := Nat.le_of_lt (Trans.trans (Trans.trans h1 h0) hj)
  have hi : 0 ≤ i'val - ival := by simp

  have : jval.succ ≤ jval.succ + (i'val - ival) := Nat.add_le_add_left hi _
  have : j'val.pred < jval.succ + (i'val - ival) := Trans.trans (Trans.trans j'val.pred_le hj) this
  have : j'val.pred < (jval.succ + i'val) - ival := Nat.add_sub_assoc h1 .. ▸ this
  have : j'val.pred < (i'val + jval.succ) - ival := Nat.add_comm .. ▸ this
  have : j'val.pred < i'val + (jval.succ - ival) := Nat.add_sub_assoc hijs .. ▸ this
  have : j'val.pred < (jval.succ - ival) + i'val := Nat.add_comm .. ▸ this
  have : j'val.pred - i'val < jval.succ - ival := Nat.sub_lt_right_of_lt_add (Nat.pred_def h0) this
  show j'val.pred.succ - i'val.succ < jval.succ - ival from Nat.succ_sub_succ_eq_sub _ _ |>.symm ▸ this


@[simp] theorem dbgTraceIfShared_noop : (dbgTraceIfShared s a) = a := rfl

def d {α : Type u} [ToString α] (val : α) (sfx: String := s!"{val}") : α := dbgTrace s!"{sfx}" (fun () => val)

namespace Interval
variable {p' a' c': Prop} {b k : Nat}
theorem closed_closed (hab : a' → (k ≤ b) → p') (hbc : (b ≤ k) → c' → p') : a' → c' → p' := fun ha hc => (Nat.le_total ..).elim (hab ha ·) (hbc · hc)
theorem open_closed (hab : a' → (k < b) → p') (hbc : (b ≤ k) → c' → p') : a' → c' → p' := fun ha hc => (Nat.lt_or_ge ..).elim (hab ha ·) (hbc · hc)
theorem closed_open (hab : a' → (k ≤ b) → p') (hbc : (b < k) → c' → p') : a' → c' → p' := fun ha hc => (Nat.lt_or_ge ..).elim (hbc · hc) (hab ha ·)

theorem superset {p q r1 r2 : Prop} (h1 : r1 → r2 → p) (h2 : p → q) : r1 → r2 → q := fun hr1 hr2 => h2 (h1 hr1 hr2)
end Interval

theorem prop_mix {p a b c  : Prop} [Decidable b]: (a →  b → p) → (¬b →  c → p) → (a →  c → p) := fun h1 h2 ha hc => (Decidable.em b).elim (h1 ha) (h2 · hc)

end utils

--------------------------- FIND NEXT I ---------------------------------
universe u
variable {α : Type u}
variable [r : LinearOrder α]


section next_i_prelims

theorem next_i_succx {arr: Array α} {ival : Nat} {hi_size : ival < arr.size} {pivot : α} (h : ∃ (i_ : Nat) (_ : i_ < arr.size), ival ≤ i_ ∧ (pivot ≤ arr[i_])) (h' : ¬ (pivot ≤ arr[ival])) : (∃ (i_ : Nat) (_ : i_ < arr.size), ival.succ ≤ i_ ∧ (pivot ≤ arr[i_])) ∧ (ival.succ < arr.size) :=
  have h1 : ∃ (i_ : Nat) (_ : i_ < arr.size), ival.succ ≤ i_ ∧ (pivot ≤ arr[i_]) :=
    let ⟨i_, _, hxi⟩ := h
    have : ival ≠ i_ := by intro; cases hxi; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]
    have : ival < i_ := mtp (Nat.eq_or_lt_of_le hxi.left) this
    have : ival.succ ≤ i_ := this
    ⟨i_, ‹_›, ⟨this, hxi.2⟩⟩

  have h2 : ival.succ < arr.size :=
    let ⟨_, hi_, ⟨hw, _⟩⟩ := h1
    Trans.trans hw hi_
  ⟨h1, h2⟩


end next_i_prelims

def next_i (arr: Array α) (ival : Nat) (hi_size : ival < arr.size) (pivot : α) (h : ∃ (i_ : Nat) (_ : i_ < arr.size), ival ≤ i_ ∧ (pivot ≤ arr[i_])) : Fin arr.size
:=
  if _ : pivot ≤ arr[ival] then
    ⟨ival, hi_size⟩
  else
    have h := next_i_succx h ‹_›
    next_i arr ival.succ h.2 pivot h.1
termination_by arr.size - ival

section next_i_is_correct
variable {arr: Array α}
theorem nexti_ge_i {i' : Fin arr.size} (_ : i' = next_i arr ival hi_size pivot h := by trivial) : ival ≤ i'.val :=
  if _ : pivot ≤ arr[ival] then
    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold next_i; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]
  else
    have h := next_i_succx h ‹_›
    let i' := next_i arr ival.succ h.2 pivot h.1

    have hi : ival.succ ≤ i'.val := nexti_ge_i
    have : ival ≤ i'.val := Nat.le_of_lt hi
    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold next_i; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]

termination_by arr.size - ival

theorem nexti_elem_not_left_of_piv {i' : Fin arr.size} (_ : i' = next_i arr ival hi_size pivot h := by trivial) : pivot ≤ arr[i'] :=
  if _ : pivot ≤ arr[ival] then
    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold next_i; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]
  else
    have h := next_i_succx h ‹_›
    let i' := next_i arr ival.succ h.2 pivot h.1

    have : (pivot ≤ arr[i']) := nexti_elem_not_left_of_piv

    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold next_i; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]
termination_by arr.size - ival

theorem next_i_before_is_left {i' : Fin arr.size} (_ : i' = next_i arr ival hi_size pivot h := by trivial) : (∀ (i_ : Nat) (_ : i_ < arr.size), ival ≤ i_ → i_ < i'.val → ¬(pivot ≤ arr[i_])) :=
  if _ : pivot ≤ arr[ival] then
    have : ∀ (i_ : Nat) (_ : i_ < arr.size), ival ≤ i_ → i_ < ival → ¬(pivot ≤ arr[i_]) := fun i_ _ h h' =>
      have := Nat.not_le_and_gt ⟨h, h'⟩
      False.elim this

    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold next_i; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]
  else
    have h := next_i_succx h ‹_›
    let i'' := next_i arr ival.succ h.2 pivot h.1

    have hi : ∀ (i_ : Nat) (_ : i_ < arr.size), ival < i_ → i_ < i''.val → ¬(pivot ≤ arr[i_]) := next_i_before_is_left

    have : ∀ (i_ : Nat) (_ : i_ < arr.size), ival ≤ i_ → i_ < i''.val → ¬(pivot ≤ arr[i_]) :=
      fun i_ _ (hi2 : ival ≤ i_ ) (hi3 : i_ < i''.val) =>
        have : ival < i_ ∨ ival = i_ := Nat.lt_or_eq_of_le hi2
        show ¬(pivot ≤ arr[i_]) from match this with
        | .inl hlt => hi i_ ‹_› hlt hi3
        | .inr heq => by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]

    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold next_i; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]
termination_by arr.size - ival


theorem nexti_first  : (pivot ≤ arr[ival]) →  (ival = next_i arr ival hi_size pivot h) := by unfold next_i; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]

end next_i_is_correct




--------------------------- FIND NEXT J ---------------------------------

section next_j_prelims

theorem next_j_predx {arr: Array α} {jval : Nat} {hj_size: jval < arr.size} {pivot : α} (h : ∃ (j_ : Nat) (_ : j_ < arr.size), j_ ≤ jval ∧ (arr[j_] ≤ pivot)) (_ : ¬(arr[jval] ≤ pivot) := by trivial) : (∃ (j_ : Nat) (_ : j_ < arr.size), j_.succ ≤ jval  ∧ (arr[j_] ≤ pivot)) ∧ (∃ (j_ : Nat) (_ : j_ < arr.size), j_ ≤ jval.pred ∧ (arr[j_] ≤ pivot)) :=
  let ⟨j_, _, hxj⟩ := h
  have : j_ ≠ jval := by intro; cases hxj; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]

  have : j_ < jval := mtp (Nat.eq_or_lt_of_le hxj.left) this

  .intro
    ⟨_, ‹_›, ⟨this, hxj.right⟩⟩
    ⟨_, ‹_›, ⟨Nat.pred_def this, hxj.right⟩⟩

theorem next_j_termin {arr: Array α} {jval : Nat} {hj_size: jval < arr.size} {pivot : α} (h : ∃ (j_ : Nat) (_ : j_ < arr.size), j_ ≤ jval ∧ (arr[j_] ≤ pivot)) (_ : ¬(arr[jval] ≤ pivot)) : jval.pred < jval :=

  have ⟨h1, _⟩ := next_j_predx h
  let ⟨_, _, ⟨hw, _⟩⟩ := h1
  show jval.pred < jval from Nat.pred_lt' hw

end next_j_prelims


def next_j (arr: Array α) (jval : Nat) (hj_size: jval < arr.size) (pivot : α) (h : ∃ (j_ : Nat) (_ : j_ < arr.size), j_ ≤ jval ∧ (arr[j_] ≤ pivot)) : Fin arr.size :=
  if hhh : arr[jval] ≤ pivot then
    ⟨jval, ‹jval < arr.size›⟩

  else

    have h3 := next_j_predx h |>.right
    next_j arr jval.pred (Trans.trans jval.pred_le hj_size) pivot h3

termination_by jval
decreasing_by apply next_j_termin ‹_› ‹_›

section next_j_is_correct
variable {arr: Array α}

theorem nextj_le_j {j' : Fin arr.size} (_ : j' = next_j arr jval hj_size pivot h := by trivial) : j'.val ≤ jval :=
  if _ : arr[jval] ≤ pivot then
    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold next_j; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]
  else
    have := next_j_predx h |>.right
    let j' := next_j arr jval.pred (Trans.trans jval.pred_le hj_size) pivot this

    have hj : j'.val ≤ jval.pred := nextj_le_j

    have : j'.val ≤ jval := Nat.le_trans hj jval.pred_le
    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold next_j; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]
termination_by jval
decreasing_by apply next_j_termin ‹_› ‹_›


theorem nextj_elem_not_right_of_piv {j' : Fin arr.size} (_ : j' = next_j arr jval hj_size pivot h := by trivial) : arr[j'] ≤ pivot :=
  if _ : arr[jval] ≤ pivot then
    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold next_j; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]
  else
    have := next_j_predx h |>.right
    let j' := next_j arr jval.pred (Trans.trans jval.pred_le hj_size) pivot this

    have : arr[j'] ≤ pivot := nextj_elem_not_right_of_piv
    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold next_j; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]
termination_by jval
decreasing_by apply next_j_termin ‹_› ‹_›

theorem next_j_before_is_right {j' : Fin arr.size} (_ : j' = next_j arr jval hj_size pivot h := by trivial) : (∀ (j_ : Nat) (_ : j_ < arr.size), j'.val < j_ → j_ ≤ jval → ¬(arr[j_] ≤ pivot)) :=

  if _ : arr[jval] ≤ pivot then

    have : ∀ (j_ : Nat) (_ : j_ < arr.size), jval < j_ → j_ ≤ jval → ¬(arr[j_] ≤ pivot) := fun j_ _ h' h =>
      have := Nat.not_le_and_gt ⟨h, h'⟩
      False.elim this

    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold next_j; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]
  else

    have := next_j_predx h ‹_› |>.right
    let j' := next_j arr jval.pred (Trans.trans jval.pred_le hj_size) pivot this

    have hj : (∀ (j_ : Nat) (_ : j_ < arr.size), j'.val < j_ → j_ ≤ jval.pred → ¬(arr[j_] ≤ pivot)) := next_j_before_is_right

    have : (∀ (j_ : Nat) (_ : j_ < arr.size), j'.val < j_ → j_ ≤ jval → ¬(arr[j_] ≤ pivot)) :=
      fun j_ _ (hj2 : j'.val < j_ ) (hj3 : j_ ≤ jval) =>
        have this : j_ < jval ∨ j_ = jval := Nat.lt_or_eq_of_le hj3
        show ¬(arr[j_] ≤ pivot) from match this with
        | .inl hlt => hj j_ ‹_› hj2 (Nat.pred_def hlt)
        | .inr heq => by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]

    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold next_j; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]
termination_by jval
decreasing_by apply next_j_termin ‹_› ‹_›

theorem nextj_first : (arr[jval] ≤ pivot) → (jval = next_j arr jval hj_size pivot h) := by unfold next_j; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]

end next_j_is_correct



------------------------------- PARTITION -------------------------------------

section part_prelims

variable {arr: Array α}

theorem part_prelims_i_1 {i' j' : Fin arr.size} (_ : i' = next_i arr ival hi pivot hxi := by trivial) (_ : j' = next_j arr jval hj pivot hxj := by trivial) (h0 : i'.val < j'.val := by trivial) : let arr' := (arr.swap i' j'); ∃ (i_ : Nat) (_ : i_ < arr'.size), i'.val.succ ≤ i_ ∧ pivot ≤ arr'[i_] :=
  let arr' := (arr.swap i' j')
  have hs_size : arr'.size = arr.size := (arr.size_swap i' j')

  show ∃ (i_ : Nat) (_ : i_ < arr'.size), i'.val.succ ≤ i_ ∧ pivot ≤ arr'[i_] from
    let j_  := {j' with isLt := hs_size.symm ▸ j'.isLt : Fin arr'.size}
    have hh0 : j'.val=j_.val := by simp
    suffices i'.val.succ ≤ j_.val ∧ pivot ≤ arr'[j_] from  ⟨j_.1, j_.2, this⟩
    suffices  pivot ≤ arr'[j_] from ⟨hh0 ▸ h0, this⟩

    have hswap_def : arr'[j_] = arr[i'] := arr.get_swap_right

    suffices pivot ≤ arr[i'] by
      simp only [←hswap_def] at *
      assumption
    nexti_elem_not_left_of_piv

theorem part_prelims_i_2 {i' j' : Fin arr.size} (_ : i' = next_i arr ival hi pivot hxi := by trivial) (_ : j' = next_j arr jval hj pivot hxj := by trivial) (h0 : i'.val < j'.val := by trivial) : let arr' := (arr.swap i' j'); i'.val.succ < arr'.size :=
  let arr' := (arr.swap i' j')

  have : ∃ (i_ : Nat) (_ : i_ < arr'.size), i'.val.succ ≤ i_ ∧ pivot ≤ arr'[i_] := part_prelims_i_1
  let ⟨i_, h2, h1, _⟩ := this

  show i'.val.succ < arr'.size from Trans.trans h1 h2

theorem part_prelims_j_1 {i' j' : Fin arr.size} (_ : i' = next_i arr ival hi pivot hxi := by trivial) (_ : j' = next_j arr jval hj pivot hxj := by trivial) (h0 : i'.val < j'.val := by trivial) : let arr' := (arr.swap i' j'); ∃ (j_ : Nat) (_ : j_ < arr'.size), j_ ≤ j'.val.pred ∧ arr'[j_] ≤ pivot :=
  let arr' := (arr.swap i' j')
  have hs_size : arr'.size = arr.size := (arr.size_swap i' j')

  show ∃ (j_ : Nat) (_ : j_ < arr'.size), j_ ≤ j'.val.pred ∧ arr'[j_] ≤ pivot from
    let i_  := {i' with isLt := hs_size.symm ▸ i'.isLt : Fin arr'.size}
    have hh0 : i'.val=i_.val := by simp

    suffices i_.val ≤ j'.val.pred ∧ arr'[i_] ≤ pivot from  ⟨i_.1, i_.2, this⟩
    suffices  arr'[i_] ≤ pivot from ⟨Nat.pred_def h0, this⟩

    have hswap_def : arr'[i_] = arr[j'] := arr.get_swap_left

    suffices  arr[j'] ≤ pivot by
      simp only [←hswap_def] at *
      assumption
    nextj_elem_not_right_of_piv

theorem part_prelims_j_2 {i' j' : Fin arr.size} (_ : i' = next_i arr ival hi pivot hxi := by trivial) (_ : j' = next_j arr jval hj pivot hxj := by trivial) : let arr' := (arr.swap i' j'); j'.val.pred < arr'.size :=
  let arr' := (arr.swap i' j')
  have hs_size : arr'.size = arr.size := (arr.size_swap i' j')

  have : j'.val < arr'.size  := hs_size.symm ▸ j'.isLt
  show j'.val.pred < arr'.size from Trans.trans j'.val.pred_le this




----------



structure Partition (α: Type u)  where
  arr' : Array α
  i' : Nat
  j' : Nat
  deriving Repr

end part_prelims

def part (arr: Array α) (ival : Nat) (hi : ival < arr.size)  (jval : Nat) (hj : jval < arr.size) (pivot : α) (hxi : ∃ (i_ : Nat) (_ : i_ < arr.size), ival ≤ i_ ∧ pivot ≤ arr[i_]) (hxj : ∃ (j_ : Nat) (_ : j_ < arr.size), j_ ≤ jval ∧ arr[j_] ≤ pivot) : Partition α :=
  let i' := next_i arr ival hi pivot hxi
  let j' := next_j arr jval hj pivot hxj

  if h0 : i'.val < j'.val then
    -- let arr' := (arr.swap i' j')
    let arr' := (dbgTraceIfShared s!"i={ival}, j={jval}\n" arr).swap i' j'

    part arr' i'.val.succ part_prelims_i_2 j'.val.pred part_prelims_j_2 pivot part_prelims_i_1 part_prelims_j_1

  else if _ : j'.val = i'.val then
    ⟨arr, i'.val.succ, j'.val.pred⟩

  else
    ⟨arr, i'.val, j'.val⟩

termination_by jval.succ - ival
decreasing_by apply nat_mix nexti_ge_i nextj_le_j; assumption



section part_correct

theorem part_perm {arr: Array α} {ival : Nat} {hi : ival < arr.size}  {jval : Nat} {hj : jval < arr.size} {pivot : α} {hxi : ∃ (i_ : Nat) (_ : i_ < arr.size), ival ≤ i_ ∧ pivot ≤ arr[i_]} {hxj : ∃ (j_ : Nat) (_ : j_ < arr.size), j_ ≤ jval ∧ arr[j_] ≤ pivot} (_ : x = part arr ival hi jval hj pivot hxi hxj := by trivial) : arr ~ x.arr' :=
  let i' := next_i arr ival hi pivot hxi
  let j' := next_j arr jval hj pivot hxj

  if h0 : i'.val < j'.val then
    let arr' := (arr.swap i' j')
    let x' := part arr' i'.val.succ part_prelims_i_2 j'.val.pred part_prelims_j_2 pivot part_prelims_i_1 part_prelims_j_1

    have h'' : arr' ~ x'.arr' := part_perm
    have : arr ~ arr' := ⟨[(i', j')], Array.swaps_one_eq_swap.symm⟩
    have : arr ~ x'.arr' := Trans.trans this h''

    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold part; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]

  else if heq : j'.val = i'.val then
    have _ : arr ~ arr := Array.Perm.refl arr
    by simp_all (config := { zetaDelta := true }) [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold part; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]

  else
    have _ : arr ~ arr := Array.Perm.refl arr
    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold part; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]

termination_by jval.succ - ival
decreasing_by apply nat_mix nexti_ge_i nextj_le_j; assumption

theorem part_arr_size {arr: Array α} {ival : Nat} {hi : ival < arr.size}  {jval : Nat} {hj : jval < arr.size} {pivot : α} {hxi : ∃ (i_ : Nat) (_ : i_ < arr.size), ival ≤ i_ ∧ pivot ≤ arr[i_]} {hxj : ∃ (j_ : Nat) (_ : j_ < arr.size), j_ ≤ jval ∧ arr[j_] ≤ pivot} (_ : x = part arr ival hi jval hj pivot hxi hxj  := by trivial) : x.arr'.size = arr.size :=
  let i' := next_i arr ival hi pivot hxi
  let j' := next_j arr jval hj pivot hxj

  if h0 : i'.val < j'.val then
    let arr' := (arr.swap i' j')
    have hs_size : arr'.size = arr.size := arr.size_swap i' j'
    let x' := part arr' i'.val.succ part_prelims_i_2 j'.val.pred part_prelims_j_2 pivot part_prelims_i_1 part_prelims_j_1

    have : x'.arr'.size = arr.size := hs_size.symm ▸ part_arr_size

    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold part; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]

  else if _ : j'.val = i'.val then
    by simp_all (config := { zetaDelta := true }) [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold part; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]

  else have _ : j'.val < i'.val := Nat.lt_of_le_of_ne (mtp (Nat.lt_or_ge i'.val j'.val) h0) ‹_›

    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold part; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]
termination_by jval.succ - ival
decreasing_by apply nat_mix nexti_ge_i nextj_le_j; assumption


theorem part_j_lt_i {arr: Array α} {ival : Nat} {hi : ival < arr.size}  {jval : Nat} {hj : jval < arr.size} {pivot : α} {hxi : ∃ (i_ : Nat) (_ : i_ < arr.size), ival ≤ i_ ∧ pivot ≤ arr[i_]} {hxj : ∃ (j_ : Nat) (_ : j_ < arr.size), j_ ≤ jval ∧ arr[j_] ≤ pivot} (_ : x = part arr ival hi jval hj pivot hxi hxj := by trivial) : x.j' < x.i' :=
  let i' := next_i arr ival hi pivot hxi
  let j' := next_j arr jval hj pivot hxj

  if h0 : i'.val < j'.val then
    let arr' := (arr.swap i' j')
    let x' := part arr' i'.val.succ part_prelims_i_2 j'.val.pred part_prelims_j_2 pivot part_prelims_i_1 part_prelims_j_1

    have : x'.j' < x'.i' := part_j_lt_i
    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold part; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]

  else if _ : j'.val = i'.val then
    have : j'.val.pred <  i'.val.succ := Trans.trans j'.val.pred_le (‹_› ▸ i'.val.lt_succ_self : _ < _)
    by simp_all (config := { zetaDelta := true }) [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold part; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]

  else have _ : j'.val < i'.val := Nat.lt_of_le_of_ne (mtp (Nat.lt_or_ge i'.val j'.val) h0) ‹_›

    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold part; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]
termination_by jval.succ - ival
decreasing_by apply nat_mix nexti_ge_i nextj_le_j; assumption


theorem part_out_i {arr: Array α} {ival : Nat} {hi : ival < arr.size}  {jval : Nat} {hj : jval < arr.size} {pivot : α} {hxi : ∃ (i_ : Nat) (_ : i_ < arr.size), ival ≤ i_ ∧ pivot ≤ arr[i_]} {hxj : ∃ (j_ : Nat) (_ : j_ < arr.size), j_ ≤ jval ∧ arr[j_] ≤ pivot} (_ : x = part arr ival hi jval hj pivot hxi hxj := by trivial) : ∀ (k_ : Nat) (_ : k_ < arr.size) (_ : k_ < x.arr'.size), ( k_ < ival → x.arr'[k_]=arr[k_] ) :=
  let i' := next_i arr ival hi pivot hxi
  let j' := next_j arr jval hj pivot hxj

  if h0 : i'.val < j'.val then
    have his : ival < i'.val.succ := Nat.lt_succ_of_le nexti_ge_i

    let arr' := (arr.swap i' j')
    have hs_size : arr'.size = arr.size := (arr.size_swap i' j')
    let x' := part arr' i'.val.succ part_prelims_i_2 j'.val.pred part_prelims_j_2 pivot part_prelims_i_1 part_prelims_j_1

    have h'' : ∀ (k_ : Nat) (_ : k_ < arr'.size) _ , ( k_ < i'.val.succ → x'.arr'[k_]=arr'[k_] )  := part_out_i

    have hsizea'' : x'.arr'.size = arr.size  := hs_size ▸ part_arr_size

    have _ : i'.val < x'.arr'.size := hsizea''.symm ▸ i'.isLt

    have : ∀ (k_ : Nat) (_ : k_ < arr.size) (_ : k_ < x'.arr'.size), ( k_ < ival → x'.arr'[k_]=arr[k_] ) := fun k_ hsk _ h1 =>

      have hsk' : k_ < (arr.swap i' j').size := hs_size ▸ ‹k_ < arr.size›
      have _ : k_ < x'.arr'.size := hsizea''.symm ▸ ‹k_ < arr.size›

      have heq1 : x'.arr'[k_] = (arr.swap  i' j')[k_] := h'' k_ ‹_› ‹_› <| Trans.trans h1 his
      have h2 : k_ < i'.val := Trans.trans h1 nexti_ge_i

      have hi : k_ ≠ i'.val := Nat.ne_of_lt h2
      have hj : k_ ≠ j'.val := Nat.ne_of_lt (Trans.trans h2 h0)
      have heq2 : (arr.swap i' j')[k_] = arr[k_]  := arr.get_swap_of_ne hsk hi hj

      show x'.arr'[k_] = arr[k_] from Trans.trans heq1 heq2
    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold part; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]

  else if _ : j'.val = i'.val then

    have : ∀ (k_ : Nat) (_ : k_ < arr.size) (_ : k_ < arr.size), ( k_ < i'.val.succ → arr[k_]=arr[k_] )  := fun _ _ _ _ => rfl
    by simp_all (config := { zetaDelta := true }) [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold part; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]

  else have _ : j'.val < i'.val := Nat.lt_of_le_of_ne (mtp (Nat.lt_or_ge i'.val j'.val) h0) ‹_›

    have : ∀ (k_ : Nat) (_ : k_ < arr.size) (_ : k_ < arr.size), ( k_ < i'.val → arr[k_]=arr[k_] )  := fun _ _ _ _ => rfl
    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold part; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]
termination_by jval.succ - ival
decreasing_by apply nat_mix nexti_ge_i nextj_le_j; assumption

theorem part_out_j {arr: Array α} {ival : Nat} {hi : ival < arr.size}  {jval : Nat} {hj : jval < arr.size} {pivot : α} {hxi : ∃ (i_ : Nat) (_ : i_ < arr.size), ival ≤ i_ ∧ pivot ≤ arr[i_]} {hxj : ∃ (j_ : Nat) (_ : j_ < arr.size), j_ ≤ jval ∧ arr[j_] ≤ pivot} (_ : x = part arr ival hi jval hj pivot hxi hxj := by trivial) : ∀ (k_ : Nat) (_ : k_ < arr.size) (_ : k_ < x.arr'.size), ( jval < k_ → x.arr'[k_]=arr[k_] ) :=
  let i' := next_i arr ival hi pivot hxi
  let j' := next_j arr jval hj pivot hxj

  if h0 : i'.val < j'.val then
    have hjp : j'.val.pred < jval := Trans.trans (Nat.pred_lt' ‹i'.val < j'.val›) nextj_le_j

    let arr' := (arr.swap i' j')
    have hs_size : arr'.size = arr.size := (arr.size_swap i' j')
    let x' := part arr' i'.val.succ part_prelims_i_2 j'.val.pred part_prelims_j_2 pivot part_prelims_i_1 part_prelims_j_1

    have h'' : ∀ (k_ : Nat) (_ : k_ < arr'.size) (_ : k_ < x'.arr'.size), ( j'.val.pred < k_ → x'.arr'[k_]=arr'[k_] ) := part_out_j

    have hsizea'' : x'.arr'.size = arr.size  := hs_size ▸ part_arr_size

    have _ : i'.val < x'.arr'.size := hsizea''.symm ▸ i'.isLt

    have : ∀ (k_ : Nat) (_ : k_ < arr.size) (_ : k_ < x'.arr'.size), ( jval < k_ → x'.arr'[k_]=arr[k_] )  := fun k_ hsk _ h1 =>

      have hsk' : k_ < (arr.swap i' j').size := hs_size ▸ ‹k_ < arr.size›
      have _ : k_ < x'.arr'.size := hsizea''.symm ▸ ‹k_ < arr.size›

      have heq1 : x'.arr'[k_] = (arr.swap  i' j')[k_] := h'' k_ ‹_› ‹_› <| Trans.trans hjp h1
      have h2 : j'.val < k_ := Trans.trans nextj_le_j h1

      have hi : k_ ≠ i'.val := Nat.ne_of_lt (Trans.trans h0 h2) |>.symm
      have hj : k_ ≠ j'.val := Nat.ne_of_lt h2 |>.symm
      have heq2 : (arr.swap i' j')[k_] = arr[k_]  := arr.get_swap_of_ne hsk hi hj
      show x'.arr'[k_] = arr[k_] from Trans.trans heq1 heq2

    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold part; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]

  else if _ : j'.val = i'.val then

    have : ∀ (k_ : Nat) (_ : k_ < arr.size) (_ : k_ < arr.size), ( j'.val.pred < k_ → arr[k_]=arr[k_] )  := fun _ _ _ _ => rfl
    by simp_all (config := { zetaDelta := true }) [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold part; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]

  else have _ : j'.val < i'.val := Nat.lt_of_le_of_ne (mtp (Nat.lt_or_ge i'.val j'.val) h0) ‹_›

    have : ∀ (k_ : Nat) (_ : k_ < arr.size) (_ : k_ < arr.size), ( j'.val < k_ → arr[k_]=arr[k_] ) := fun _ _ _ _ => rfl
    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold part; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]
termination_by jval.succ - ival
decreasing_by apply nat_mix nexti_ge_i nextj_le_j; assumption

set_option maxHeartbeats 5000000 in
theorem part_correctness_i {arr: Array α} {ival : Nat} {hi : ival < arr.size}  {jval : Nat} {hj : jval < arr.size} {pivot : α} {hxi : ∃ (i_ : Nat) (_ : i_ < arr.size), ival ≤ i_ ∧ pivot ≤ arr[i_]} {hxj : ∃ (j_ : Nat) (_ : j_ < arr.size), j_ ≤ jval ∧ arr[j_] ≤ pivot} (_ : x = part arr ival hi jval hj pivot hxi hxj := by trivial) : ∀ (k_ : Nat) (_ : k_ < x.arr'.size), (ival  ≤ k_→k_ <  x.i' → x.arr'[k_] ≤ pivot) :=
  let i' := next_i arr ival hi pivot hxi
  let j' := next_j arr jval hj pivot hxj

  if h0 : i'.val < j'.val then
    let arr' := (arr.swap i' j')
    have hs_size : arr'.size = arr.size := (arr.size_swap i' j')
    let x' := part arr' i'.val.succ part_prelims_i_2 j'.val.pred part_prelims_j_2 pivot part_prelims_i_1 part_prelims_j_1

    have h'' : ∀ (k_ : Nat) (_ : k_ < x'.arr'.size), (i'.val.succ  ≤ k_→k_ <  x'.i' →  x'.arr'[k_] ≤ pivot) := part_correctness_i
    have h_out'' : ∀ (k_ : Nat) (_ : k_ < arr'.size) (_ : k_ < x'.arr'.size), (k_ < i'.val.succ → x'.arr'[k_] = arr'[k_]) := part_out_i
    have hsizea'' : x'.arr'.size = arr.size  := hs_size ▸ part_arr_size

    have _ : i'.val < x'.arr'.size := hsizea''.symm ▸ i'.isLt

    have : ∀ (k_ : Nat) _, (ival  ≤ k_→k_ <  x'.i' →  x'.arr'[k_] ≤ pivot) := fun k_ _ =>

      have hhh1 (h1 : ival ≤ k_) (h2 : k_ < i'.val) : x'.arr'[k_] ≤ pivot :=
        have hsk : k_ < arr.size := Trans.trans h2 i'.isLt
        have hsk' : k_ < (arr.swap i' j').size := hs_size ▸ ‹k_ < arr.size›
        have _ : k_ < x'.arr'.size := hsizea''.symm ▸ ‹k_ < arr.size›

        have : ¬(pivot ≤ arr[k_]) := next_i_before_is_left rfl k_ ‹_› ‹_› ‹_›
        have : arr[k_] ≤ pivot := le_of_not_le this
        have : (arr.swap i' j')[k_] ≤ pivot :=

          have hi : k_ ≠ i'.val := Nat.ne_of_lt h2
          have hj : k_ ≠ j'.val := Nat.ne_of_lt (Trans.trans h2 h0)
          have heq : (arr.swap i' j')[k_] = arr[k_]  := arr.get_swap_of_ne hsk hi hj

          show (arr.swap i' j')[k_] ≤ pivot from heq.symm ▸ this

        show x'.arr'[k_] ≤ pivot from
          have heq : x'.arr'[k_] = (arr.swap i' j')[k_] := h_out'' k_ ‹_› ‹_›  <| Trans.trans h2 (i'.val.lt_succ_self)

          heq.symm ▸ this

      have hhh2 : i'.val ≤ k_ → k_ ≤ i'.val → x'.arr'[k_] ≤ pivot :=
        have : x'.arr'[i'.val] ≤ pivot :=
          have : arr[j'] ≤ pivot := nextj_elem_not_right_of_piv rfl
          have hswap_def : (arr.swap i' j')[i'] = arr[j'] := arr.get_swap_left
          have : (arr.swap i' j')[i'] ≤ pivot := hswap_def.symm ▸ this
          show  x'.arr'[i'] ≤ pivot from
            have heq : x'.arr'[i'] = (arr.swap i' j')[i'] :=
              h_out'' i'.val (hs_size.symm ▸ i'.isLt) ‹i'.val < x'.arr'.size›
              <| i'.val.lt_succ_self
            heq.symm ▸ this

        fun h1 h2 =>
          have _ : k_ < arr.size := Trans.trans h2 i'.isLt

          have heq : i'.val = k_ := Nat.le_antisymm h1 h2
          show x'.arr'[k_] ≤ pivot by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le, heq]

      have : ival ≤ k_ → k_ ≤ i'.val → x'.arr'[k_] ≤ pivot  := prop_mix hhh1 ((Nat.not_lt_eq _ _ |>.symm) ▸ hhh2)
      have : ival ≤ k_ → k_ < i'.val.succ → x'.arr'[k_] ≤ pivot :=
        have hlt_succ_iff : k_ < Nat.succ i'.val ↔ k_ ≤ i'.val := ⟨Nat.le_of_lt_succ, Nat.lt_succ_of_le⟩
        by rw [←hlt_succ_iff] at this; assumption

      have h'' : ¬(k_ < i'.val.succ) → k_ < x'.i' → x'.arr'[k_] ≤ pivot := (Nat.not_lt_eq _ _ |>.symm) ▸  h'' k_ ‹_›

      prop_mix this h''

    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold part; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]

  else if heq : j'.val = i'.val then

    have : ∀ (k_ : Nat) (_ : k_ < arr.size), (ival  ≤ k_→k_ <  i'.val.succ →  arr[k_] ≤ pivot) := fun k_ _ =>
      have h1' : ival  ≤ k_ → k_ < i'.val →  arr[k_] ≤ pivot := fun h1 h2 => le_of_not_le (next_i_before_is_left rfl k_ ‹_› h1 h2)

      have h2' : ¬(k_ < i'.val) → k_ < i'.val.succ →  arr[k_] ≤ pivot := fun h1 h2 =>
        have h1 : i'.val ≤ k_ := Nat.ge_of_not_lt h1
        have h2 : k_ ≤ i'.val := Nat.le_of_lt_succ h2

        have _ : arr[j'.val] ≤ pivot := nextj_elem_not_right_of_piv
        have _ : k_ = j'.val := heq.symm ▸ Nat.le_antisymm h2 h1

        by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]

      prop_mix h1' h2'

    by simp_all (config := { zetaDelta := true }) [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold part; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]

  else have _ : j'.val < i'.val := Nat.lt_of_le_of_ne (mtp (Nat.lt_or_ge i'.val j'.val) h0) ‹_›

    have : ∀ (k_ : Nat) (_ : k_ < arr.size), (ival  ≤ k_→k_ <  i'.val →  arr[k_] ≤ pivot) := fun k_ _ h1 h2 =>
      le_of_not_le (next_i_before_is_left rfl k_ ‹_› h1 h2)

    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold part; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]
termination_by jval.succ - ival
decreasing_by apply nat_mix nexti_ge_i nextj_le_j; assumption

set_option maxHeartbeats 5000000 in
theorem part_correctness_j {arr: Array α} {ival : Nat} {hi : ival < arr.size}  {jval : Nat} {hj : jval < arr.size} {pivot : α} {hxi : ∃ (i_ : Nat) (_ : i_ < arr.size), ival ≤ i_ ∧ pivot ≤ arr[i_]} {hxj : ∃ (j_ : Nat) (_ : j_ < arr.size), j_ ≤ jval ∧ arr[j_] ≤ pivot} (_ : x = part arr ival hi jval hj pivot hxi hxj := by trivial) : ∀ (k_ : Nat) (_ : k_ < x.arr'.size), (x.j'  < k_→k_ ≤  jval → pivot ≤ x.arr'[k_]) :=
  let i' := next_i arr ival hi pivot hxi
  let j' := next_j arr jval hj pivot hxj

  if h0 : i'.val < j'.val then

    let arr' := (arr.swap i' j')
    have hs_size : arr'.size = arr.size := (arr.size_swap i' j')
    let x' := part arr' i'.val.succ part_prelims_i_2 j'.val.pred part_prelims_j_2 pivot part_prelims_i_1 part_prelims_j_1

    have h'' : ∀ (k_ : Nat) _, (x'.j'  < k_→k_ ≤  j'.val.pred →  pivot ≤ x'.arr'[k_]) := part_correctness_j
    have h_out'' : ∀ (k_ : Nat) (_ : k_ < arr'.size) (_ : k_ < x'.arr'.size), (  j'.val.pred < k_ → x'.arr'[k_]=arr'[k_] ) := part_out_j

    have hsizea'' : x'.arr'.size = arr.size  := hs_size ▸ part_arr_size

    have _ : j'.val < x'.arr'.size := hsizea''.symm ▸ j'.isLt

    have : ∀ (k_ : Nat) _, (x'.j'  < k_→k_ ≤  jval →  pivot ≤ x'.arr'[k_]) :=  fun k_ _ =>

      have hhh2 : j'.val < k_ → k_ ≤ jval → pivot ≤ x'.arr'[k_] := fun  (h1 : j'.val < k_) (h2 : k_ ≤ jval) =>
        have hsk : k_ < arr.size := Trans.trans h2 hj
        have hsk' : k_ < (arr.swap i' j').size := hs_size ▸ ‹k_ < arr.size›
        have _ : k_ < x'.arr'.size := hsizea''.symm ▸ ‹k_ < arr.size›

        have : ¬(arr[k_] ≤ pivot):= next_j_before_is_right rfl k_ ‹_› ‹_› ‹_›
        have : pivot ≤ arr[k_] := le_of_not_le this
        have : pivot ≤ (arr.swap i' j')[k_] :=
          have hi : k_ ≠ i'.val := Nat.ne_of_lt (Trans.trans h0 h1) |>.symm
          have hj : k_ ≠ j'.val := Nat.ne_of_lt h1 |>.symm
          have heq : (arr.swap i' j')[k_] = arr[k_]  := arr.get_swap_of_ne hsk hi hj

          show pivot ≤ (arr.swap i' j')[k_] from heq.symm ▸ this


        show pivot ≤ x'.arr'[k_] from
          have heq : x'.arr'[k_] = (arr.swap i' j')[k_] := h_out'' k_ ‹_› ‹_›  <| Trans.trans (Nat.pred_lt' h0) h1
          heq.symm ▸ this

      have hhh1 : j'.val ≤ k_ → k_ ≤ j'.val → pivot ≤ x'.arr'[k_] :=
        have : pivot ≤ x'.arr'[j'.val] :=
          have : pivot ≤ arr[i'] := nexti_elem_not_left_of_piv rfl
          have hswap_def : (arr.swap i' j')[j'] = arr[i'] := arr.get_swap_right
          have : pivot ≤ (arr.swap i' j')[j'] := hswap_def.symm ▸ this
          show  pivot ≤ x'.arr'[j'] from
            have heq : x'.arr'[j'] = (arr.swap i' j')[j'] :=
              h_out'' j'.val (hs_size |>.symm ▸ j'.isLt) ‹j'.val < x'.arr'.size›
              <| (Nat.pred_lt' h0)
            heq.symm ▸ this

        fun h1 h2 =>
          have _ : k_ < arr.size := Trans.trans h2 j'.isLt

          have heq : j'.val = k_ := Nat.le_antisymm h1 h2
          show pivot ≤ x'.arr'[k_] by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le, heq]

      have heq : (j'.val < k_) = ¬(k_ ≤ j'.val) := Nat.not_le_eq _ _ |>.symm

      have : j'.val ≤ k_ → k_ ≤ jval → pivot ≤ x'.arr'[k_] := prop_mix hhh1 (heq ▸  hhh2)
      have : j'.val.pred < k_ → k_ ≤ jval → pivot ≤ x'.arr'[k_] := fun h1 h2 =>
        have h1 : j'.val ≤ k_ := Nat.succ_pred (Nat.not_eq_zero_of_lt h0) ▸ h1
        this h1 h2
      have h'' : x'.j' < k_ → k_ ≤ j'.val.pred → pivot ≤ x'.arr'[k_] := h'' k_ ‹_›

      have heq : (j'.val.pred < k_) = ¬(k_ ≤ j'.val.pred) := Nat.not_le_eq _ _ |>.symm
      prop_mix h'' ( heq ▸ this)
    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold part; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]

  else if heq : j'.val = i'.val then
    have : ∀ (k_ : Nat) (_ : k_ < arr.size), (j'.val.pred  < k_→k_ ≤  jval →  pivot ≤ arr[k_]) := fun k_ _  =>
      have h1' : ¬(k_ ≤ j'.val) → k_ ≤ jval → pivot ≤ arr[k_] := fun h1 h2 => le_of_not_le (next_j_before_is_right rfl k_ ‹_› (Nat.gt_of_not_le h1) h2)
      have h2' : j'.val.pred < k_ → k_ ≤ j'.val →  pivot ≤ arr[k_] := fun h1 h2 =>

        have hle_of_pred_lt {m n : Nat} : m.pred < n → m ≤ n := -- Nat.le_of_pred_lt Available in Mathlib.Data.Nat.Basic (v4.0.0) or Mathlib.Data.Nat.Defs (master branch)
          match m with
          | 0 => Nat.le_of_lt
          | .succ _ => id
        have h1 : j'.val ≤ k_ := hle_of_pred_lt h1
        have h2 : k_ ≤ j'.val := h2

        have _ : pivot ≤ arr[i'.val] := nexti_elem_not_left_of_piv
        have _ : k_ = i'.val := heq.symm ▸ Nat.le_antisymm h2 h1

        by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]
      prop_mix h2' h1'

    by simp_all (config := { zetaDelta := true }) [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold part; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]

  else have _ : j'.val < i'.val := Nat.lt_of_le_of_ne (mtp (Nat.lt_or_ge i'.val j'.val) h0) ‹_›
    have : ∀ (k_ : Nat) (_ : k_ < arr.size), (j'.val  < k_→k_ ≤  jval →  pivot ≤ arr[k_]) := fun k_ _  h1 h2 =>
      le_of_not_le (next_j_before_is_right rfl k_ ‹_› h1 h2)
    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold part; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]
termination_by jval.succ - ival
decreasing_by apply nat_mix nexti_ge_i nextj_le_j; assumption

set_option maxHeartbeats 5000000 in
theorem part_invariance {arr: Array α} {ival : Nat} {hi : ival < arr.size}  {jval : Nat} {hj : jval < arr.size} {pivot : α} {hxi : ∃ (i_ : Nat) (_ : i_ < arr.size), ival ≤ i_ ∧ pivot ≤ arr[i_]} {hxj : ∃ (j_ : Nat) (_ : j_ < arr.size), j_ ≤ jval ∧ arr[j_] ≤ pivot} (motive : α → Prop) (_ : x = part arr ival hi jval hj pivot hxi hxj := by trivial) : (∀ (k_ : Nat) (_ : k_ < arr.size) (_ : ival ≤ k_) (_ : k_ ≤ jval), (motive arr[k_]) ) → (∀ (k_ : Nat) (_ : k_ < x.arr'.size) (_ : ival ≤ k_) (_ : k_ ≤ jval), (motive x.arr'[k_])) :=
  let i' := next_i arr ival hi pivot hxi
  let j' := next_j arr jval hj pivot hxj

  if h0 : i'.val < j'.val then
    let arr' := (arr.swap i' j')
    have hs_size : arr'.size = arr.size := (arr.size_swap i' j')
    let x' := part arr' i'.val.succ part_prelims_i_2 j'.val.pred part_prelims_j_2 pivot part_prelims_i_1 part_prelims_j_1

    have his : ival < i'.val.succ := Nat.lt_succ_of_le nexti_ge_i
    have hjp : j'.val.pred < jval := Trans.trans (Nat.pred_lt' ‹i'.val < j'.val›) nextj_le_j

    -- arr'[i'.val.succ : j'.val.pred] ≤ v → x'.arr'[i'.val.succ : j'.val.pred] ≤ v
    have h'' : (∀ (k_ : Nat) (_ : k_ < arr'.size) (_ : i'.val.succ ≤ k_) (_ : k_ ≤ j'.val.pred), (motive arr'[k_]) ) → (∀ (k_ : Nat) (_ : k_ < x'.arr'.size) (_ : i'.val.succ ≤ k_) (_ : k_ ≤ j'.val.pred), (motive x'.arr'[k_])) := part_invariance motive

    -- arr[ival : jval] ≤ v → arr'[ival : jval] ≤ v
    have h1'' : (∀ (k_ : Nat) (_ : k_ < arr.size) (_ : ival ≤ k_) (_ : k_ ≤ jval), (motive arr[k_]) ) → (∀ (k_ : Nat) (_ : k_ < arr'.size) (_ : ival ≤ k_) (_ : k_ ≤ jval), (motive arr'[k_])) := fun h_ k_ (hsk' : k_ < arr'.size) (hik : ival ≤ k_) (hkj : k_ ≤ jval) =>

      have hsk : k_ < arr.size := hs_size ▸ ‹k_ < arr'.size›

      if hki' : i' = k_ then
        have hh0 : motive arr[j'] :=
          have : ival ≤ i'.val := (nexti_ge_i)
          have hhi : ival ≤ j'.val := Nat.le_of_lt (Trans.trans this h0)
          have hhj : j'.val ≤ jval := (nextj_le_j)
          h_ j'.1 j'.2 hhi hhj

        have hh1 : arr'[k_] = arr[j'] :=
          have : arr'.get ⟨i'.1, hs_size.symm  ▸ i'.2⟩ = arr.get j' := show arr'[i'] = arr[j'] from arr.get_swap_left
          show arr'.get ⟨k_, hki' ▸ hs_size.symm  ▸ i'.2⟩ = arr.get j' from  hki' ▸ this

        show motive arr'[k_] from  hh1.symm ▸ hh0

      else if hjk' : j' = k_ then
        have hh0 : motive arr[i'] :=
          have : j'.val ≤ jval := (nextj_le_j)
          have hhj : i'.val ≤ jval := Nat.le_of_lt (Trans.trans h0 this)
          have hhi : ival ≤ i'.val := (nexti_ge_i)
          h_ i'.1 i'.2 hhi hhj

        have hh1 : arr'[k_] = arr[i'] :=
          have hswap_def : (arr.swap i' j')[j'] = arr[i'] := arr.get_swap_right
          have : arr'.get ⟨j'.1, hs_size.symm  ▸ j'.2⟩ = arr.get i' := show arr'[j'] = arr[i'] from hswap_def
          show arr'.get ⟨k_, hjk' ▸ hs_size.symm  ▸ j'.2⟩ = arr.get i' from  hjk' ▸ this

        show motive arr'[k_] from  hh1.symm ▸ hh0

      else
        have hout : arr'[k_] = arr[k_]  := arr.get_swap_of_ne hsk (Ne.symm hki') (Ne.symm hjk')
        have hh0 : motive arr[k_] := h_ k_ ‹_› hik hkj
        show motive arr'[k_] from hout.symm ▸ hh0

    -- arr'[ival : jval] ≤ v → x'.arr'[ival : jval] ≤ v
    have h2'' : (∀ (k_ : Nat) (_ : k_ < arr'.size) (_ : ival ≤ k_) (_ : k_ ≤ jval), (motive arr'[k_]) ) → (∀ (k_ : Nat) (_ : k_ < x'.arr'.size) (_ : ival ≤ k_) (_ : k_ ≤ jval), (motive x'.arr'[k_])) :=  fun h_ k_ (_ : k_ < x'.arr'.size) (hik : ival ≤ k_) (hkj : k_ ≤ jval) =>

      have _ : k_ < arr'.size := (show x'.arr'.size = arr'.size from part_arr_size) ▸ ‹k_ < x'.arr'.size›

      have : motive arr'[k_] := h_ k_ ‹_› hik hkj

      if hki' : k_ < i'.val.succ then
        have hout : x'.arr'[k_]=arr'[k_] := (part_out_i) k_ ‹_› ‹_› hki'
        show motive x'.arr'[k_] from hout.symm ▸ this

      else if hjk' : j'.val.pred < k_ then
        have hout : x'.arr'[k_]=arr'[k_] := (part_out_j) k_ ‹_› ‹_› hjk'
        show motive x'.arr'[k_] from hout.symm ▸ this

      else have hki' : i'.val.succ ≤ k_ := Nat.ge_of_not_lt ‹_›; have hjk' : k_ ≤ j'.val.pred := Nat.ge_of_not_lt ‹_›;
        have : ∀ (k_ : Nat) (_ : k_ < arr'.size) (_ : i'.val.succ ≤ k_) (_ : k_ ≤ j'.val.pred), (motive arr'[k_]) := fun kk_ _ hhik' hhkj' =>
          have _ : ival ≤ kk_ := Trans.trans his hhik' |> Nat.le_of_lt
          have _ : kk_ ≤ jval := Trans.trans hhkj' hjp |> Nat.le_of_lt

          show motive arr'[kk_] from h_ kk_ ‹_› ‹_› ‹_›
        show motive x'.arr'[k_] from h'' this k_ ‹_› hki' hjk'


    -- arr[ival : jval] ≤ v → x'.arr'[ival : jval] ≤ v
    have : (∀ (k_ : Nat) (_ : k_ < arr.size) (_ : ival ≤ k_) (_ : k_ ≤ jval), (motive arr[k_]) ) → (∀ (k_ : Nat) (_ : k_ < x'.arr'.size) (_ : ival ≤ k_) (_ : k_ ≤ jval), (motive x'.arr'[k_])) := (· |> h1'' |> h2'')

    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold part; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]
  else if heq : j'.val = i'.val then
    by simp_all (config := { zetaDelta := true }) [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold part; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]
  else have _ : j'.val < i'.val := Nat.lt_of_le_of_ne (mtp (Nat.lt_or_ge i'.val j'.val) h0) ‹_›
    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold part; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]
termination_by jval.succ - ival
decreasing_by apply nat_mix nexti_ge_i nextj_le_j; assumption








private theorem xi_elim {arr: Array α} {right : Nat} (h : ∃ (i_ : Nat) (_ : i_ < arr.size), ival ≤ i_ ∧ i_ ≤ right ∧ pivot ≤ arr[i_] := by trivial) :  ∃ (i_ : Nat) (_ : i_ < arr.size), ival ≤ i_ ∧ pivot ≤ arr[i_] := let ⟨_, _, _, _, _⟩ := h; ⟨‹_›, _, ‹_›, ‹_›⟩
private theorem xj_elim {arr: Array α} {left : Nat} (h : ∃ (j_ : Nat) (_ : j_ < arr.size), left ≤ j_ ∧ j_ ≤ jval ∧ arr[j_] ≤ pivot := by trivial) :  ∃ (j_ : Nat) (_ : j_ < arr.size), j_ ≤ jval ∧ arr[j_] ≤ pivot := let ⟨_, _, _, _, _⟩ := h; ⟨‹_›, _, ‹_›, ‹_›⟩

section part_aux_lemmas

section lemma_prelims

variable {arr: Array α} {i' j' : Fin arr.size}

theorem part_prelims_gen_i  (_ : i' = next_i arr ival hi pivot hxi := by trivial) (_ : j' = next_j arr jval hj pivot hxj := by trivial) (hjr : jval ≤ right := by trivial) (h0 : i'.val < j'.val := by trivial) : let arr' := (arr.swap i' j'); ∃ (i_ : Nat) (_ : i_ < arr'.size), (i'.val.succ ≤ i_) ∧ (i_ ≤ right) ∧ (pivot ≤ arr'[i_]) :=
  let arr' := (arr.swap i' j')
  have hs_size : arr'.size = arr.size := (arr.size_swap i' j')
  have hsj' : j'.val < arr'.size := hs_size.symm ▸ j'.isLt

  show ∃ (i_ : Nat) (_ : i_ < arr'.size), (i'.val.succ ≤ i_) ∧ (i_ ≤ right) ∧ (pivot ≤ arr'[i_]) from
      let j_ : Fin arr'.size := ⟨j'.val, hs_size.symm ▸ j'.isLt ⟩
      have hh0 : j'.val=j_.val := by simp
      suffices i'.val.succ ≤ j_.val ∧ j_.val ≤ right ∧ (pivot ≤ arr'[j_]) from  ⟨j_.1, j_.2, this⟩
      suffices (pivot ≤ arr'[j_]) from ⟨hh0 ▸ h0, hh0 ▸ Trans.trans nextj_le_j hjr, this⟩

      have hswap_def : arr'[j_] = arr[i'] := arr.get_swap_right

      suffices  (pivot ≤ arr[i']) by
        simp only [←hswap_def] at *
        assumption
      nexti_elem_not_left_of_piv



theorem part_prelims_gen_j (_ : i' = next_i arr ival hi pivot hxi := by trivial) (_ : j' = next_j arr jval hj pivot hxj := by trivial) (hli : left ≤ ival := by trivial) (h0 : i'.val < j'.val := by trivial) : let arr' := (arr.swap i' j'); ∃ (j_ : Nat) (_ : j_ < arr'.size), (left ≤ j_) ∧ (j_ ≤ j'.val.pred) ∧ (arr'[j_] ≤ pivot) :=
  let arr' := (arr.swap i' j')
  have hs_size : arr'.size = arr.size := (arr.size_swap i' j')

  show ∃ (j_ : Nat) (_ : j_ < arr'.size), (left ≤ j_) ∧ (j_ ≤ j'.val.pred) ∧ (arr'[j_] ≤ pivot) from
      let i_ : Fin arr'.size := ⟨i', hs_size.symm ▸ i'.isLt ⟩
      have hh0 : i'.val=i_.val := by simp

      suffices left ≤ i_.val ∧ i_.val ≤ j'.val.pred ∧ (arr'[i_] ≤ pivot) from  ⟨i_.1, i_.2, this⟩
      suffices  (arr'[i_] ≤ pivot) from ⟨hh0 ▸ Trans.trans hli nexti_ge_i, Nat.pred_def h0, this⟩

      have hswap_def : arr'[i_] = arr[j'] := arr.get_swap_left

      suffices  (arr[j'] ≤ pivot) by
        simp only [←hswap_def] at *
        assumption
      nextj_elem_not_right_of_piv


theorem part_prelims_i_2' (hleft : ∀ (i_ : Nat) (_ : i_ < arr.size), left ≤ i_ → i_ < ival → arr[i_] ≤ pivot := by trivial) (_ : i' = next_i arr ival hi pivot hxi := by trivial) (_ : j' = next_j arr jval hj pivot hxj := by trivial) (h0 : i'.val < j'.val := by trivial) : let arr' := (arr.swap i' j');  ∀ (k_ : Nat) (_ : k_ < arr'.size), left ≤ k_ → k_ < i'.val.succ → arr'[k_] ≤ pivot :=
  let arr' := (arr.swap i' j')
  have hs_size : arr'.size = arr.size := (arr.size_swap i' j')

  show ∀ (k_ : Nat) (_ : k_ < arr'.size), left ≤ k_ → k_ < i'.val.succ → arr'[k_] ≤ pivot from
    fun k_ hsk' =>
      have hsk : k_ < arr.size := hs_size ▸ ‹k_ < arr'.size›
      have h_out_i :  k_ < i'.val → arr'[k_]=arr[k_]  := fun h2 =>
        have hi : k_ ≠ i'.val := Nat.ne_of_lt h2
        have hj : k_ ≠ j'.val := Nat.ne_of_lt (Trans.trans h2 h0)
        show (arr.swap i' j')[k_] = arr[k_] from arr.get_swap_of_ne hsk hi hj


      have h1 : left ≤ k_ → k_ < ival → arr[k_] ≤ pivot := hleft k_ ‹_›

      have : ival ≤ k_ → k_ < i'.val → ¬(pivot ≤ arr[k_]) := (next_i_before_is_left) k_ ‹_›
      have h2 : ival ≤ k_ → k_ < i'.val → arr[k_] ≤ pivot := Interval.superset this le_of_not_le

      have h_ : left ≤ k_ → k_ < i'.val → arr'[k_] ≤ pivot := fun h' (h : k_ < i'.val) =>
        (h_out_i h).symm ▸ (Interval.open_closed h1 h2 h' h)

      have h3 : i'.val ≤ k_ → k_ ≤ i'.val → arr'[k_] ≤ pivot :=
        have : (arr'[i'.val] ≤ pivot) :=
          have : (arr[j'] ≤ pivot) := nextj_elem_not_right_of_piv
          have hswap_def : (arr.swap i' j')[i']= arr[j'] := arr.get_swap_left
          show  (arr'[i'] ≤ pivot) from hswap_def.symm ▸ this

        fun hh1 hh2 =>
          have heq1 : i'.val = k_ := Nat.le_antisymm hh1 hh2
          have heq2 : arr'[i'.val] = arr'[k_] := by simp [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le, heq1]
          show (arr'[k_] ≤ pivot) from heq2 ▸ this

      have h4 : i'.val < k_ → k_ < i'.val.succ → arr'[k_] ≤ pivot := fun hh1 hh2 => (Nat.not_le_and_gt ⟨hh1, hh2⟩).elim

      Interval.open_closed h_ (Interval.closed_open h3 h4)


theorem part_prelims_j_2' (hright : ∀ (j_ : Nat) (_ : j_ < arr.size), jval < j_ → j_ ≤ right → pivot ≤ arr[j_] := by trivial) (_ : i' = next_i arr ival hi pivot hxi := by trivial) (_ : j' = next_j arr jval hj pivot hxj := by trivial) (h0 : i'.val < j'.val := by trivial) : let arr' := (arr.swap i' j'); ∀ (k_ : Nat) (x : k_ < arr'.size), j'.val.pred  < k_ → k_ ≤ right → pivot ≤ arr'[k_] :=
  let arr' := (arr.swap i' j')
  have hs_size : arr'.size = arr.size := (arr.size_swap i' j')
  have hsj' : j'.val < arr'.size := hs_size.symm ▸ j'.isLt

  show ∀ (k_ : Nat) (x : k_ < arr'.size), j'.val.pred  < k_ → k_ ≤ right → pivot ≤ arr'[k_] from
    fun k_ hsk' =>
      have hsk : k_ < arr.size := hs_size ▸ ‹k_ < arr'.size›
      have h_out_j :  j'.val < k_ → arr'[k_]=arr[k_] := fun h2 =>
        have hi : k_ ≠ i'.val := Nat.ne_of_lt (Trans.trans h0 h2) |>.symm
        have hj : k_ ≠ j'.val := Nat.ne_of_lt h2 |>.symm

        show (arr.swap i' j')[k_] = arr[k_] from  arr.get_swap_of_ne hsk hi hj

      have h1 : jval < k_ → k_ ≤ right → pivot ≤ arr[k_] := hright k_ ‹_›

      have : j'.val < k_ → k_ ≤ jval → ¬(arr[k_] ≤ pivot) := (next_j_before_is_right) k_ ‹_›
      have h2 : j'.val < k_ → k_ ≤ jval → pivot ≤ arr[k_] := Interval.superset this le_of_not_le

      have h_ : j'.val < k_ → k_ ≤ right → pivot ≤ arr'[k_] := fun (h : j'.val < k_) h' => (h_out_j h).symm ▸ (Interval.closed_open h2 h1 h h')

      have h3 : j'.val ≤ k_ → k_ ≤ j'.val → pivot ≤ arr'[k_] :=
        have : pivot ≤ arr'[j'.val] :=
          have : pivot ≤ arr[i'] := nexti_elem_not_left_of_piv
          have hswap_def : (arr.swap i' j')[j'] = arr[i'] := arr.get_swap_right
          have : pivot ≤ (arr.swap i' j')[j'] := hswap_def.symm ▸ this
          show  pivot ≤ arr'[j'] from
            have heq : arr'[j'] = (arr.swap i' j')[j'] := rfl
            heq.symm ▸ this

        fun h1 h2 =>
          have heq1 : j'.val = k_ := Nat.le_antisymm h1 h2
          have heq2 : arr'[j'.val] = arr'[k_] := by simp [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le, heq1]
          show pivot ≤ arr'[k_] from heq2 ▸ this

      have h4 : j'.val.pred < k_ → k_ < j'.val → pivot ≤ arr'[k_] := fun hh1 hh2 =>
        have hh1 : j'.val ≤ k_ := Nat.succ_pred (Nat.not_eq_zero_of_lt h0) ▸ hh1
        (Nat.not_le_and_gt ⟨hh1, hh2⟩).elim

      Interval.closed_open (Interval.open_closed h4 h3)  h_

end lemma_prelims

set_option maxHeartbeats 500000 in
private theorem part_i_gt_and_j_lt_aux {x : Partition α} (hxri : ∃ (i_ : Nat) (_ : i_ < arr.size), ival ≤ i_ ∧ i_ ≤ right ∧ pivot ≤ arr[i_]) (hxlj : ∃ (j_ : Nat) (_ : j_ < arr.size), left ≤ j_ ∧ j_ ≤ jval ∧ arr[j_] ≤ pivot) ( hli : left ≤ ival ) ( hjr : jval ≤ right ) (_ : x = part arr ival hi jval hj pivot xi_elim xj_elim := by trivial)     (_ : left < right  := by trivial) :  (left < x.i') ∧ (x.j' < right) :=

  have hxi : ∃ (i_ : Nat) (_ : i_ < arr.size), ival ≤ i_ ∧ pivot ≤ arr[i_] := xi_elim
  have hxj : ∃ (j_ : Nat) (_ : j_ < arr.size), j_ ≤ jval ∧ arr[j_] ≤ pivot := xj_elim
  let i' := next_i arr ival hi pivot hxi
  let j' := next_j arr jval hj pivot hxj

  have halli : ∀ (i_ : Nat) (_ : i_ < arr.size), ival ≤ i_ → i_ < i'.val → ¬(pivot ≤ arr[i_]) := next_i_before_is_left
  have hallj : ∀ (j_ : Nat) (_ : j_ < arr.size), j'.val < j_ → j_ ≤ jval → ¬(arr[j_] ≤ pivot) := next_j_before_is_right

  if h0 : i'.val < j'.val then
    let arr' := (arr.swap i' j')

    have his : ival < i'.val.succ := Nat.lt_succ_of_le nexti_ge_i
    have hjp : j'.val.pred < jval := Trans.trans (Nat.pred_lt' ‹i'.val < j'.val›) nextj_le_j

    have _ : ∃ (i_ : Nat) (_ : i_ < arr'.size), (i'.val.succ ≤ i_) ∧ (i_ ≤ right) ∧ (pivot ≤ arr'[i_]) := part_prelims_gen_i
    have _ : ∃ (j_ : Nat) (_ : j_ < arr'.size), (left ≤ j_) ∧ (j_ ≤ j'.val.pred) ∧ (arr'[j_] ≤ pivot) := part_prelims_gen_j

    let x' := part arr' i'.val.succ part_prelims_i_2 j'.val.pred part_prelims_j_2 pivot xi_elim xj_elim

    have _ : left ≤ i'.val.succ  := Nat.le_of_lt (Trans.trans hli his)
    have _ : j'.val.pred ≤ right:= Nat.le_of_lt (Trans.trans hjp hjr)


    have : left < x'.i' ∧ x'.j' < right := part_i_gt_and_j_lt_aux ‹_› ‹_› ‹_› ‹_›

    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold part; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]

  else if heq : j'.val = i'.val then

    have _ : left < i'.val.succ :=
      let ⟨j_, hj_, hh1, hh2, hh⟩ := hxlj

      have : ¬(j' < j_) := fun h => absurd hh (hallj j_ hj_ h hh2)
      have : j_ ≤ j' := Nat.ge_of_not_lt this

      -- so left ≤ (j_ ≤ j') = i' < i'.succ
      Trans.trans hh1 (Trans.trans this (Trans.trans heq i'.val.lt_succ_self))

    have _ : j'.val.pred < right :=
      let ⟨i_, hi_, hh1, hh2, hh⟩ := hxri

      have : ¬(i_ < i') := fun h => absurd hh (halli i_ hi_ hh1 h)
      have : i' ≤ i_ := Nat.ge_of_not_lt this

      have : j'.val ≤ right :=  Trans.trans heq (Trans.trans this hh2)

      show j'.val.pred < right from match hj_0 : j'.val with
      | 0 =>
        have : 0 < right := Nat.zero_lt_of_lt ‹left < right›
        have : j'.val < right := hj_0.symm ▸ this

        have := Trans.trans j'.val.pred_le this
        by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]
      | .succ n =>
        Trans.trans (show n.succ.pred < n.succ by simp_arith) (hj_0 ▸ this)


    by simp_all (config := { zetaDelta := true }) [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold part; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]

  else have hlt : j'.val < i'.val := Nat.lt_of_le_of_ne (mtp (Nat.lt_or_ge i'.val j'.val) h0) ‹_›

    have _ : left < i'.val :=
      let ⟨j_, hj_, hh1, hh2, hh⟩ := hxlj

      have : ¬(j' < j_) := fun h => absurd hh (hallj j_ hj_ h hh2)
      have : j_ ≤ j' := Nat.ge_of_not_lt this

      -- so left ≤ (j_ ≤ j') < i'
      Trans.trans hh1 (Trans.trans this hlt)

    have _ : j'.val < right :=
      let ⟨i_, hi_, hh1, hh2, hh⟩ := hxri

      have : ¬(i_ < i') := fun h => absurd hh (halli i_ hi_ hh1 h)
      have : i' ≤ i_ := Nat.ge_of_not_lt this

      -- so j' < (i' ≤ i_) ≤ right
      Trans.trans hlt (Trans.trans this hh2)


    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold part; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]
termination_by jval.succ - ival
decreasing_by apply nat_mix nexti_ge_i nextj_le_j; assumption

private theorem part_diff_one_of_jlti {arr: Array α} {hi_size : ival < arr.size} {hj_size : jval < arr.size} {i' : Fin arr.size} {j' : Fin arr.size} (hxri : ∃ (i_ : Nat) (_ : i_ < arr.size), ival ≤ i_ ∧ i_ ≤ right ∧ pivot ≤ arr[i_]) (hxlj : ∃ (j_ : Nat) (_ : j_ < arr.size), left ≤ j_ ∧ j_ ≤ jval ∧ arr[j_] ≤ pivot) (hilejsucc : (jval < ival) → (ival = jval.succ)) (hleft : ∀ (i_ : Nat) (_ : i_ < arr.size), left ≤ i_ → i_ < ival → arr[i_] ≤ pivot) (hright : ∀ (j_ : Nat) (_ : j_ < arr.size), jval < j_ → j_ ≤ right → pivot ≤ arr[j_]) (_ : i' = next_i arr ival hi_size pivot xi_elim := by trivial) (_ : j' = next_j arr jval hj_size pivot xj_elim := by trivial) (hji' : j'.val < i'.val := by trivial) : i'.val = j'.val.succ :=
  have hi'r : i'.val ≤ right :=
    let ⟨i_, hi_, hh1, hh2, hh⟩ := hxri

    have : ¬(i_ < i') := fun h => absurd hh (next_i_before_is_left ‹_› i_ hi_ hh1 h)
    have : i' ≤ i_ := Nat.ge_of_not_lt this

    -- so (i' ≤ i_) ≤ right
    Trans.trans this hh2

  have hlj' : left ≤ j'.val :=
    let ⟨j_, hj_, hh1, hh2, hh⟩ := hxlj

    have : ¬(j' < j_) := fun h => absurd hh (next_j_before_is_right ‹_› j_ hj_ h hh2)
    have : j_ ≤ j' := Nat.ge_of_not_lt this

    -- so left ≤ (j_ ≤ j')
    Trans.trans hh1 this

  have hir : ival ≤ right := Trans.trans (nexti_ge_i ‹_›) hi'r
  have hlj : left ≤ jval := Trans.trans hlj' (nextj_le_j ‹_›)


  if _ : jval < ival then
    have  : pivot ≤ arr[ival] := hright ival ‹_› ‹_› ‹_›
    have hi : ival = i'.val := ‹i' = _› ▸ nexti_first this

    have : arr[jval] ≤ pivot := hleft jval ‹_› ‹_› ‹_›
    have hj : jval = j'.val := ‹j' = _› ▸ nextj_first this

    show i'.val = j'.val.succ from hi ▸ hj ▸ hilejsucc ‹_›
  else

    suffices j'.val.succ ≥ i'.val from Nat.le_antisymm this hji'
    suffices ¬(j'.val.succ < i'.val) from Nat.ge_of_not_lt this

    let k' := j'.val.succ
    have hijout : k' ≤ jval ∨ ival ≤ k' :=
      suffices ¬(jval < k') ∨ ¬(k' < ival) from match this with
        | .inl h => .inl (Nat.ge_of_not_lt h)
        | .inr h => .inr (Nat.ge_of_not_lt h)
      suffices ¬(jval < k' ∧ k' < ival) from Decidable.not_and_iff_or_not _ _ |>.mp this
      fun h => ‹¬ jval < ival› (Trans.trans h.1 h.2)

    have hk1 : j'.val < k' := Nat.lt_succ_self _
    show ¬(j'.val.succ < i'.val) from fun hk2 : k' < i'.val =>
      have _ : k' < arr.size := Trans.trans hk2 i'.isLt

      have hh : arr[k'] = pivot :=
        have h1 : arr[k'] ≤ pivot :=
          if _ : k' < ival then
            hleft ‹_› ‹_› (Nat.le_of_lt (Trans.trans hlj' hk1)) ‹_›

          else have _ : ival ≤ k' := Nat.ge_of_not_lt ‹_›
            le_of_not_le (next_i_before_is_left ‹_› ‹_› ‹_› ‹_› ‹_›)

        have h2 : pivot ≤ arr[k'] :=
          if _ : jval < k' then
            hright ‹_› ‹_› ‹_› (Nat.le_of_lt (Trans.trans hk2 hi'r))

          else have _ : k' ≤ jval := Nat.ge_of_not_lt ‹_›
            le_of_not_le (next_j_before_is_right ‹_› ‹_› ‹_› ‹_› ‹_›)

        le_antisymm h1 h2

      have hh' : arr[k'] ≠ pivot := match hijout with
      | .inl h => suffices pivot < arr[k'] from ne_of_gt this
        lt_of_not_ge (next_j_before_is_right ‹_› ‹_› ‹_› ‹_› ‹_›)
      | .inr h => suffices arr[k'] < pivot from ne_of_lt this
        lt_of_not_ge (next_i_before_is_left ‹_› ‹_› ‹_› ‹_› ‹_›)

      absurd hh hh'

set_option maxHeartbeats 5000000
private theorem part_diff_one {x : Partition α}  (hxri : ∃ (i_ : Nat) (_ : i_ < arr.size), ival ≤ i_ ∧ i_ ≤ right ∧ pivot ≤ arr[i_]) (hxlj : ∃ (j_ : Nat) (_ : j_ < arr.size), left ≤ j_ ∧ j_ ≤ jval ∧ arr[j_] ≤ pivot) (hilejsucc : (jval < ival) → (ival = jval.succ)) (hli : left ≤ ival) (hjr : jval ≤ right) (hleft : ∀ (i_ : Nat) (_ : i_ < arr.size), left ≤ i_ → i_ < ival → arr[i_] ≤ pivot) (hright : ∀ (j_ : Nat) (_ : j_ < arr.size), jval < j_ → j_ ≤ right → pivot ≤ arr[j_]) (_ : x = part arr ival hi jval hj pivot xi_elim xj_elim := by trivial)     (_ : left < right := by trivial) : (ival.pred ≤ x.j') ∧ (x.i' ≤ jval.succ) :=
  have hxi : ∃ (i_ : Nat) (_ : i_ < arr.size), ival ≤ i_ ∧ pivot ≤ arr[i_] := xi_elim
  have hxj : ∃ (j_ : Nat) (_ : j_ < arr.size), j_ ≤ jval ∧ arr[j_] ≤ pivot := xj_elim
  let i' := next_i arr ival hi pivot hxi
  let j' := next_j arr jval hj pivot hxj

  if h0 : i'.val < j'.val then
    let arr' := (arr.swap i' j')

    have _ : ∃ (i_ : Nat) (_ : i_ < arr'.size), (i'.val.succ ≤ i_) ∧ (i_ ≤ right) ∧ (pivot ≤ arr'[i_]) := part_prelims_gen_i
    have _ : ∃ (j_ : Nat) (_ : j_ < arr'.size), (left ≤ j_) ∧ (j_ ≤ j'.val.pred) ∧ (arr'[j_] ≤ pivot) := part_prelims_gen_j

    let x' := part arr' i'.val.succ part_prelims_i_2 j'.val.pred part_prelims_j_2 pivot xi_elim xj_elim

    have _ : left ≤ i'.val.succ  :=
      have his : ival < i'.val.succ := Nat.lt_succ_of_le nexti_ge_i
      Nat.le_of_lt (Trans.trans hli his)

    have _ : j'.val.pred ≤ right :=
      have hjp : j'.val.pred < jval := Trans.trans (Nat.pred_lt' ‹i'.val < j'.val›) nextj_le_j
      Nat.le_of_lt (Trans.trans hjp hjr)

    have hilejsucc' : (j'.val.pred < i'.val.succ) → (i'.val.succ = j'.val.pred.succ) := fun h : j'.val.pred.succ ≤ i'.val.succ =>
      have : i'.val.succ ≤ j'.val.pred.succ := (Nat.succ_pred (Nat.not_eq_zero_of_lt h0)).symm ▸ h0
      Nat.succ_pred (Nat.not_eq_zero_of_lt h0) ▸ Nat.le_antisymm this h


    have  h'' : (i'.val.succ.pred ≤ x'.j') ∧ (x'.i' ≤ j'.val.pred.succ)  := part_diff_one ‹_› ‹_› hilejsucc' ‹_› ‹_› part_prelims_i_2' part_prelims_j_2' rfl

    have  : ival.pred ≤ x'.j' :=
      Trans.trans ival.pred_le (Trans.trans (nexti_ge_i) h''.left)

    have  : x'.i' ≤ jval.succ :=
      have h''_right : x'.i' ≤ j'.val := Nat.succ_pred (Nat.not_eq_zero_of_lt h0) ▸ h''.right
      have : jval ≤ jval.succ := Nat.le_of_lt jval.lt_succ_self
      Trans.trans h''_right (Trans.trans  (nextj_le_j) this)

    by simp [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le, *]; unfold part; simp [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le, *]

  else if heq : j'.val = i'.val then
    have : ival.pred ≤ j'.val.pred :=
      suffices ival.pred ≤ i'.val.pred from heq.symm ▸ this
      Nat.pred_le_pred (nexti_ge_i)

    have : i'.val.succ ≤ jval.succ :=
      suffices j'.val.succ ≤ jval.succ from heq ▸ this
      Nat.succ_le_succ (nextj_le_j)

    by simp_all (config := { zetaDelta := true }) [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold part; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]

  else have hlt : j'.val < i'.val := Nat.lt_of_le_of_ne (mtp (Nat.lt_or_ge i'.val j'.val) h0) ‹_›
    have hone_diff : i'.val = j'.val.succ := part_diff_one_of_jlti hxri hxlj hilejsucc hleft hright rfl rfl hlt

    have : ival.pred ≤ j'.val :=
      suffices ival ≤ j'.val.succ from Nat.pred_le_pred this
      have : ival ≤ i'.val :=  (nexti_ge_i)

      Trans.trans this hone_diff

    have : i'.val ≤ jval.succ :=
      have : j'.val.succ ≤ jval.succ := Nat.succ_le_succ (nextj_le_j)

      Trans.trans hone_diff this

    by simp_all (config := { zetaDelta := true }) [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold part; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]
termination_by jval.succ - ival
decreasing_by apply nat_mix nexti_ge_i nextj_le_j; assumption




end part_aux_lemmas



theorem part_bounds {arr: Array α} {ival : Nat} {_ : ival < arr.size}  {jval : Nat} {_ : jval < arr.size} {pivot : α} (_ : ∃ (i_ : Nat) (_ : i_ < arr.size), ival ≤ i_ ∧ i_ ≤ jval ∧ pivot ≤ arr[i_]) (_ : ∃ (j_ : Nat) (_ : j_ < arr.size), ival ≤ j_ ∧ j_ ≤ jval ∧ arr[j_] ≤ pivot) (_ : x = part arr ival ‹_› jval ‹_› pivot xi_elim xj_elim := by trivial ) (_ : ival < jval  := by trivial ) : (ival < x.i' ∧ (x.i' ≤ jval.succ)) ∧ ((ival.pred ≤ x.j') ∧ (x.j' < jval)) :=
  have hxi : ∃ (i_ : Nat) (_ : i_ < arr.size), ival ≤ i_ ∧ pivot ≤ arr[i_] := xi_elim
  have hxj : ∃ (j_ : Nat) (_ : j_ < arr.size), j_ ≤ jval ∧ arr[j_] ≤ pivot := xj_elim

  have _ : ival ≤ ival := Nat.le_refl ..
  have _ : jval ≤ jval := Nat.le_refl ..
  have h1 : (ival < x.i') ∧ (x.j' < jval) := part_i_gt_and_j_lt_aux ‹_› ‹_› ‹_› ‹_› ‹_›

  have _ : jval < ival → ival = jval.succ := fun h => Nat.lt_asymm' ⟨h, ‹_›⟩ |>.elim
  have _ : ∀ (i_ : Nat) (_ : i_ < arr.size), ival ≤ i_ → i_ < ival → (arr[i_] ≤ pivot) := fun _ _ h1 h2 => Nat.not_le_and_gt ⟨h1, h2⟩ |>.elim
  have _ : ∀ (j_ : Nat) (_ : j_ < arr.size), jval < j_ → j_ ≤ jval → (pivot ≤ arr[j_]) := fun _ _ h1 h2 => Nat.not_le_and_gt ⟨h2, h1⟩ |>.elim

  have h2 : (ival.pred ≤ x.j') ∧ (x.i' ≤ jval.succ) := part_diff_one ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  ⟨⟨h1.left, h2.right⟩, ⟨h2.left, h1.right⟩⟩





theorem part_correctness_left {arr: Array α} {ival : Nat} {hi : ival < arr.size}  {jval : Nat} {hj : jval < arr.size} {pivot : α} {hxi : ∃ (i_ : Nat) (_ : i_ < arr.size), ival ≤ i_ ∧ pivot ≤ arr[i_]} {hxj : ∃ (j_ : Nat) (_ : j_ < arr.size), j_ ≤ jval ∧ arr[j_] ≤ pivot} (_ : x = part arr ival hi jval hj pivot hxi hxj  := by trivial) : ∀ (i_ : Nat) (_ : i_ < x.arr'.size), ( ival ≤  i_→i_  ≤ x.j' → x.arr'[i_] ≤ pivot )  := fun i_ _ _ _ => (part_correctness_i) i_ ‹_› ‹_› (Trans.trans ‹_› part_j_lt_i)



theorem part_correctness_right {arr: Array α} {ival : Nat} {hi : ival < arr.size}  {jval : Nat} {hj : jval < arr.size} {pivot : α} {hxi : ∃ (i_ : Nat) (_ : i_ < arr.size), ival ≤ i_ ∧ pivot ≤ arr[i_]} {hxj : ∃ (j_ : Nat) (_ : j_ < arr.size), j_ ≤ jval ∧ arr[j_] ≤ pivot} (_ : x = part arr ival hi jval hj pivot hxi hxj  := by trivial) : ∀ (j_ : Nat) (_ : j_ < x.arr'.size), ( x.i' ≤  j_ →j_  ≤ jval → pivot ≤ x.arr'[j_] )  := fun j_ _ _ _ => (part_correctness_j) j_ ‹_› (Trans.trans part_j_lt_i ‹_›)  ‹_›

theorem part_correctness_mid {arr: Array α} {ival : Nat} {hi : ival < arr.size}  {jval : Nat} {hj : jval < arr.size} {pivot : α} (_ : ∃ (i_ : Nat) (_ : i_ < arr.size), ival ≤ i_ ∧ i_ ≤ jval ∧ pivot ≤ arr[i_]) (_ : ∃ (j_ : Nat) (_ : j_ < arr.size), ival ≤ j_ ∧ j_ ≤ jval ∧ arr[j_] ≤ pivot) (_ : x = part arr ival hi jval hj pivot xi_elim xj_elim  := by trivial) (_ : ival < jval  := by trivial ) : ∀ (p_ : Nat) (_ : p_ < x.arr'.size), ( (x.j' < p_) → (p_  < x.i') → x.arr'[p_] = pivot )  :=

  have h0 : (x.i' ≤ jval.succ) ∧ (ival.pred ≤ x.j') := have := part_bounds ‹_› ‹_›; ⟨this.left.right, this.right.left⟩
  fun p_ _ _ _ =>

  have hhhi : x.arr'[p_] ≤ pivot :=
    have : ival ≤ p_ :=
      if h1 : x.j' < ival then
        have : x.j' = ival.pred :=
          have hh1 : x.j' ≤ ival.pred := by have _ := Nat.pred_le_pred h1; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]
          (Nat.le_antisymm hh1 h0.right)

        have : ival.pred.succ ≤ p_ := this ▸ ‹x.j' < p_›
        Nat.succ_pred (Nat.not_eq_zero_of_lt h1) ▸ this
      else have h1 : ival ≤ x.j' := Nat.ge_of_not_lt ‹_›
        have : ival < p_ := Trans.trans h1 ‹x.j' < p_›
        Nat.le_of_lt this
    (part_correctness_i ‹_› p_ ‹_› · ‹_›) this

  have hhhj : pivot ≤ x.arr'[p_] :=
    have : p_ ≤ jval :=
      if h1 : jval < x.i' then
        have : x.i' = jval.succ := Nat.le_antisymm h0.left h1

        have : p_.succ ≤ jval.succ := this ▸ ‹p_  < x.i'›
        Nat.le_of_succ_le_succ this
      else have h1 : x.i' ≤ jval := Nat.ge_of_not_lt ‹_›

        have : p_  <  jval := Trans.trans ‹p_  < x.i'› h1
        Nat.le_of_lt this
    (part_correctness_j ‹_› p_ ‹_› ‹_›) this

  le_antisymm hhhi hhhj


end part_correct


-------------------- Quicksort ----------------

section qs_prelims

theorem xhr_size {arr : Array β} {left : Nat} {right : Nat} (hr_size' : right ≤ arr.size.pred := by first | simp | trivial) (hlr : left < right := by trivial) : right < arr.size :=
  have : left < arr.size.pred := Trans.trans hlr hr_size'
  have : left < arr.size := Trans.trans this arr.size.pred_le

  have hr_size' : right.succ ≤ arr.size.pred.succ := Nat.succ_le_succ hr_size'
  Nat.succ_pred (Nat.not_eq_zero_of_lt this) ▸ hr_size'

theorem xhl_size {arr : Array β} {left : Nat} {right : Nat} (hr_size' : right ≤ arr.size.pred := by first | simp | trivial) (hlr : left < right := by trivial) : left < arr.size := Trans.trans hlr xhr_size


structure GeneralPivot (arr : Array α) (left : Nat) (right : Nat) where
  val : α -- pivot value
  hx_left : ∃ (i_ : Nat) (_ : i_ < arr.size), left ≤ i_ ∧ i_ ≤ right ∧ val ≤ arr[i_]
  hx_right : ∃ (j_ : Nat) (_ : j_ < arr.size), left ≤ j_ ∧ j_ ≤ right ∧ arr[j_] ≤ val

instance {arr : Array α} {left : Nat} {right : Nat} : CoeOut (GeneralPivot arr left right) α where coe v := v.val

abbrev NormalPivot (arr : Array α) (left : Nat) (right : Nat) := {pivot : α // ∃ (p_ : Nat) (_ : p_ < arr.size) (_ : left ≤ p_) (_ : p_ ≤ right),  arr[p_] = pivot}

def NormalPivot.toGeneral {arr : Array α} {left : Nat} {right : Nat} (v : NormalPivot arr left right) : GeneralPivot arr left right :=

  have  hx_left : ∃ (i_ : Nat) (_ : i_ < arr.size), left ≤ i_ ∧ i_ ≤ right ∧ v.val ≤ arr[i_] :=
    let ⟨p_, hp_size, hlp, hpr, harrp_eq_v ⟩ := v.property
    have : v.val ≤ arr[p_] := le_of_eq harrp_eq_v.symm
    ⟨p_, hp_size, hlp, hpr, this⟩

  have  hx_right : ∃ (j_ : Nat) (_ : j_ < arr.size), left ≤ j_ ∧ j_ ≤ right ∧ arr[j_] ≤ v.val :=
    let ⟨p_, hp_size, hlp, hpr, harrp_eq_v ⟩ := v.property
    have : arr[p_] ≤ v.val := le_of_eq harrp_eq_v
    ⟨p_, hp_size, hlp, hpr, this⟩

  ⟨v.val, hx_left, hx_right⟩

instance {arr : Array α} {left : Nat} {right : Nat} : Coe (NormalPivot arr left right) (GeneralPivot arr left right) := ⟨NormalPivot.toGeneral⟩


def PivotFactory (α : Type u) [LinearOrder α] := ∀ (arr : Array α) (left right : Nat), right ≤ arr.size.pred → left < right → GeneralPivot arr left right

-- arithmetic average of left and right
def avgPivot : PivotFactory α := fun (arr : Array α) (left right : Nat) (hr_size' : right ≤ arr.size.pred) (hlr : left < right) =>
    let avg := left + ((right - left)/2)

    have hlr' : left ≤ right := Nat.le_of_lt hlr
    have : left ≤ avg ∧ avg ≤ right := Nat.avg_bounds hlr' rfl

    have _ : avg < arr.size :=  Trans.trans this.right xhr_size
    let pivot := arr[avg]
    have : ∃ (p_ : Nat) (_ : p_ < arr.size) (_ : left ≤ p_) (_ : p_ ≤ right),  arr[p_] = pivot := ⟨avg, ‹_›, this.left, this.right, rfl⟩
    show NormalPivot arr left right from ⟨pivot, this⟩

instance : Inhabited (PivotFactory α) where default := avgPivot

end qs_prelims

def qs (arr : Array α) (left := 0) (right := arr.size.pred) (hr_size' : right ≤ arr.size.pred := by first | simp | trivial) (pivotFactory : PivotFactory α := default) : {a : Array α // a.size = arr.size} :=

  if hlr : left < right then
    let pivot := pivotFactory _ _ _ hr_size' hlr
    have _ := pivot.hx_left; have _ := pivot.hx_right

    let x := part arr left xhl_size right xhr_size pivot xi_elim xj_elim

    /- termination Proof -/
    have : x.j' < right := part_bounds ‹_› ‹_› |>.right.right
    have _ : x.j' - left < right - left := Nat.sub_lt_sub hlr this

    have : left < x.i' := part_bounds ‹_› ‹_› |>.left.left
    have _ : right - x.i' < right - left := Nat.sub_lt_sub_left hlr this
    /- QED termination Proof -/

    have arr'_property : x.arr'.size = arr.size := part_arr_size

    have : right ≤ x.arr'.size.pred := arr'_property.symm ▸ hr_size'
    have hj_size' : x.j' ≤ x.arr'.size.pred := Nat.le_of_lt (Trans.trans (part_bounds ‹_› ‹_› |>.right.right) this)
    let arr'' := qs x.arr' left x.j' hj_size' pivotFactory

    have hr_size'' : right ≤ arr''.val.size.pred := arr''.property.symm ▸ arr'_property.symm ▸ hr_size'
    let arr'''  := qs arr'' x.i' right hr_size'' pivotFactory

    have : arr'''.val.size  = arr.size := Trans.trans (Trans.trans arr'''.property arr''.property) arr'_property
    ⟨arr'''.val, this⟩
  else
    ⟨arr, by simp⟩
termination_by right - left


section qs_correct

section qs_monotonic_prelim

set_option maxHeartbeats 5000000 in
theorem qs_out_left {arr : Array α} {left right : Nat} {hr_size' : right ≤ arr.size.pred} {pivotFactory : PivotFactory α} {q : {a : Array α // a.size = arr.size } } (h : q = qs arr left right hr_size' pivotFactory := by trivial) : ∀ (k_ : Nat) (_ : k_ < arr.size) (_ : k_ < q.val.size), (k_ < left) → (q.val[k_] = arr[k_]) :=

  if hlr : left < right then
    let pivot := pivotFactory _ _ _ hr_size' hlr
    have _ := pivot.hx_left; have _ := pivot.hx_right

    let x := part arr left xhl_size right xhr_size pivot xi_elim xj_elim

    /- termination Proof -/
    have : x.j' < right := part_bounds ‹_› ‹_› |>.right.right
    have _ : x.j' - left < right - left := Nat.sub_lt_sub hlr this

    have : left < x.i' := part_bounds ‹_› ‹_› |>.left.left
    have _ : right - x.i' < right - left := Nat.sub_lt_sub_left hlr this
    /- QED termination Proof -/

    have arr'_property : x.arr'.size = arr.size := part_arr_size

    have : right ≤ x.arr'.size.pred := arr'_property.symm ▸ hr_size'
    have hj_size' : x.j' ≤ x.arr'.size.pred := Nat.le_of_lt (Trans.trans (part_bounds ‹_› ‹_› |>.right.right) this)
    let arr'' := qs x.arr' left x.j' hj_size' pivotFactory
    have h'' : ∀ (k_ : Nat) (_ : k_ < x.arr'.size)(_ : k_ < arr''.val.size), (k_ < left) → (arr''.val[k_] = x.arr'[k_]) := qs_out_left

    have hr_size'' : right ≤ arr''.val.size.pred := arr''.property.symm ▸ arr'_property.symm ▸ hr_size'
    let arr'''  := qs arr'' x.i' right hr_size'' pivotFactory
    have h''' : ∀ (k_ : Nat) (_ : k_ < arr''.val.size)(_ : k_ < arr'''.val.size), (k_ < x.i') → (arr'''.val[k_] = arr''.val[k_]) := qs_out_left

    have : ∀ (k_ : Nat) (_ : k_ < arr.size) (_ : k_ < arr'''.val.size), (k_ < left) → (arr'''.val[k_] = arr[k_]) := fun k_ _ _ (h : k_ < left)  =>
      have _ : k_ < x.arr'.size := arr'_property.symm ▸ ‹k_ < arr.size›
      have _ : k_ < arr''.val.size := arr'''.property ▸ ‹k_ < arr'''.val.size›

      have hh1 : x.arr'[k_] = arr[k_] := (part_out_i) k_ ‹_› ‹_› h
      have hh2 : arr''.val[k_] = x.arr'[k_] := h'' k_ ‹_› ‹_› h
      have hh3 : arr'''.val[k_] = arr''.val[k_] := h''' k_ ‹_› ‹_› (Trans.trans h (part_bounds ‹_› ‹_› |>.left.left))
      show arr'''.val[k_] = arr[k_] from Trans.trans hh3 (Trans.trans hh2 hh1)

    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold qs; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]
  else
    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold qs; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]
termination_by right - left


set_option maxHeartbeats 5000000 in
theorem qs_out_right {arr : Array α} {left right : Nat} {hr_size' : right ≤ arr.size.pred} {pivotFactory : PivotFactory α} {q : {a : Array α // a.size = arr.size } } (h : q = qs arr left right hr_size' pivotFactory := by trivial) : ∀ (k_ : Nat) (_ : k_ < arr.size) (_ : k_ < q.val.size), (right < k_) → (q.val[k_] = arr[k_]) :=

  if hlr : left < right then
    let pivot := pivotFactory _ _ _ hr_size' hlr
    have _ := pivot.hx_left; have _ := pivot.hx_right

    let x := part arr left xhl_size right xhr_size pivot xi_elim xj_elim

    /- termination Proof -/
    have : x.j' < right := part_bounds ‹_› ‹_› |>.right.right
    have _ : x.j' - left < right - left := Nat.sub_lt_sub hlr this

    have : left < x.i' := part_bounds ‹_› ‹_› |>.left.left
    have _ : right - x.i' < right - left := Nat.sub_lt_sub_left hlr this
    /- QED termination Proof -/

    have arr'_property : x.arr'.size = arr.size := part_arr_size

    have : right ≤ x.arr'.size.pred := arr'_property.symm ▸ hr_size'
    have hj_size' : x.j' ≤ x.arr'.size.pred := Nat.le_of_lt (Trans.trans (part_bounds ‹_› ‹_› |>.right.right) this)
    let arr'' := qs x.arr' left x.j' hj_size' pivotFactory
    have h'' : ∀ (k_ : Nat) (_ : k_ < x.arr'.size)(_ : k_ < arr''.val.size), (x.j' < k_) → (arr''.val[k_] = x.arr'[k_]) := qs_out_right

    have hr_size'' : right ≤ arr''.val.size.pred := arr''.property.symm ▸ arr'_property.symm ▸ hr_size'
    let arr'''  := qs arr'' x.i' right hr_size'' pivotFactory
    have h''' : ∀ (k_ : Nat) (_ : k_ < arr''.val.size)(_ : k_ < arr'''.val.size), (right < k_) → (arr'''.val[k_] = arr''.val[k_]) := qs_out_right

    have : ∀ (k_ : Nat) (_ : k_ < arr.size) (_ : k_ < arr'''.val.size), (right < k_) → (arr'''.val[k_] = arr[k_]) := fun k_ _ _ (h : right < k_)  =>
      have _ : k_ < x.arr'.size := arr'_property.symm ▸ ‹k_ < arr.size›
      have _ : k_ < arr''.val.size := arr'''.property ▸ ‹k_ < arr'''.val.size›

      have hh1 : x.arr'[k_] = arr[k_] := (part_out_j) k_ ‹_› ‹_› h
      have hh2 : arr''.val[k_] = x.arr'[k_] := h'' k_ ‹_› ‹_› (Trans.trans (part_bounds ‹_› ‹_› |>.right.right) h)
      have hh3 : arr'''.val[k_] = arr''.val[k_] := h''' k_ ‹_› ‹_› h
      show arr'''.val[k_] = arr[k_] from Trans.trans hh3 (Trans.trans hh2 hh1)

    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold qs; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]
  else
    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold qs; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]
termination_by right - left


set_option maxHeartbeats 50000000 in
theorem qs_invariance {arr : Array α} {left right : Nat} {hr_size' : right ≤ arr.size.pred} {pivotFactory : PivotFactory α} {q : {a : Array α // a.size = arr.size } } (motive : α → Prop) (h : q = qs arr left right hr_size' pivotFactory := by trivial) :  (∀ (k_ : Nat) (_ : k_ < arr.size) (_ : left ≤ k_) (_ : k_ ≤ right), (motive arr[k_]) ) → (∀ (k_ : Nat) (_ : k_ < q.val.size) (_ : left ≤ k_) (_ : k_ ≤ right), (motive q.val[k_])) :=

  if hlr : left < right then
    let pivot := pivotFactory _ _ _ hr_size' hlr
    have _ := pivot.hx_left; have _ := pivot.hx_right

    let x := part arr left xhl_size right xhr_size pivot xi_elim xj_elim

    -- arr[left : right] ≤ v → x'.arr'[left : right] ≤ v
    have h''1 : (∀ (k_ : Nat) (_ : k_ < arr.size) (_ : left ≤ k_) (_ : k_ ≤ right), (motive arr[k_]) ) → (∀ (k_ : Nat) (_ : k_ < x.arr'.size) (_ : left ≤ k_) (_ : k_ ≤ right), (motive x.arr'[k_])) := part_invariance motive

    /- termination Proof -/
    have : x.j' < right := part_bounds ‹_› ‹_› |>.right.right
    have _ : x.j' - left < right - left := Nat.sub_lt_sub hlr this

    have : left < x.i' := part_bounds ‹_› ‹_› |>.left.left
    have _ : right - x.i' < right - left := Nat.sub_lt_sub_left hlr this
    /- QED termination Proof -/

    have arr'_property : x.arr'.size = arr.size := part_arr_size

    have : right ≤ x.arr'.size.pred := arr'_property.symm ▸ hr_size'
    have hj_size' : x.j' ≤ x.arr'.size.pred := Nat.le_of_lt (Trans.trans (part_bounds ‹_› ‹_› |>.right.right) this)
    let arr'' := qs x.arr' left x.j' hj_size' pivotFactory
    -- arr'[left : j'] ≤ v → arr''[left : j'] ≤ v
    have h'' : (∀ (k_ : Nat) (_ : k_ < x.arr'.size) (_ : left ≤ k_) (_ : k_ ≤ x.j'), (motive x.arr'[k_]) ) → (∀ (k_ : Nat) (_ : k_ < arr''.val.size) (_ : left ≤ k_) (_ : k_ ≤ x.j'), (motive arr''.val[k_])) := qs_invariance motive

    -- arr'[left : right] ≤ v → arr''[left : right] ≤ v
    have h''2 : (∀ (k_ : Nat) (_ : k_ < x.arr'.size) (_ : left ≤ k_) (_ : k_ ≤ right), (motive x.arr'[k_]) ) → (∀ (k_ : Nat) (_ : k_ < arr''.val.size) (_ : left ≤ k_) (_ : k_ ≤ right), (motive arr''.val[k_])) := fun h_ k_ (_ : k_ < arr''.val.size) (hlk : left ≤ k_) (hkr : k_ ≤ right) =>
      have _ : k_ < x.arr'.size := arr''.property ▸ ‹k_ < arr''.val.size›

      if hkj : k_ ≤ x.j' then
        have : ∀ (k_ : Nat) (_ : k_ < x.arr'.size) (_ : left ≤ k_) (_ : k_ ≤ x.j'), (motive x.arr'[k_]) := fun kk_ _ hhlk hhkj =>
          show motive x.arr'[kk_] from h_ kk_ ‹_› hhlk (Nat.le_of_lt (Trans.trans hhkj ‹x.j' < right›))
        show motive arr''.val[k_] from h'' this k_ ‹_› hlk hkj
      else have hkj : x.j' < k_ := Nat.gt_of_not_le hkj
        have hout : arr''.val[k_] = x.arr'[k_] := (qs_out_right) k_ ‹_› ‹_› hkj
        have : motive x.arr'[k_] := h_ k_ ‹_› hlk hkr
        show motive arr''.val[k_] from hout.symm ▸ this



    have hr_size'' : right ≤ arr''.val.size.pred := arr''.property.symm ▸ arr'_property.symm ▸ hr_size'
    let arr'''  := qs arr'' x.i' right hr_size'' pivotFactory
    -- arr''[i' : right] ≤ v → arr'''[i' : right] ≤ v
    have h''' : (∀ (k_ : Nat) (_ : k_ < arr''.val.size) (_ : x.i' ≤ k_) (_ : k_ ≤ right), (motive arr''.val[k_]) ) → (∀ (k_ : Nat) (_ : k_ < arr'''.val.size) (_ : x.i' ≤ k_) (_ : k_ ≤ right), (motive arr'''.val[k_])) := qs_invariance motive

    -- arr''[left : right] ≤ v → arr'''[left : right] ≤ v
    have h''3 : (∀ (k_ : Nat) (_ : k_ < arr''.val.size) (_ : left ≤ k_) (_ : k_ ≤ right), (motive arr''.val[k_]) ) → (∀ (k_ : Nat) (_ : k_ < arr'''.val.size) (_ : left ≤ k_) (_ : k_ ≤ right), (motive arr'''.val[k_])) := fun h_ k_ (_ : k_ < arr'''.val.size) (hlk : left ≤ k_) (hkr : k_ ≤ right) =>
      have _ : k_ < arr''.val.size := arr'''.property ▸ ‹k_ < arr'''.val.size›

      if hki : x.i' ≤ k_ then
        have : ∀ (k_ : Nat) (_ : k_ < arr''.val.size) (_ : x.i' ≤ k_) (_ : k_ ≤ right), (motive arr''.val[k_]) := fun kk_ _ hhik hhkr =>
          show motive arr''.val[kk_] from h_ kk_ ‹_› (Nat.le_of_lt (Trans.trans ‹left < x.i'› hhik)) hhkr
        show motive arr'''.val[k_] from h''' this k_ ‹_› hki hkr
      else have hki : k_ < x.i' := Nat.gt_of_not_le hki
        have hout : arr'''.val[k_] = arr''.val[k_] := (qs_out_left) k_ ‹_› ‹_› hki
        have : motive arr''.val[k_] := h_ k_ ‹_› hlk hkr
        show motive arr'''.val[k_] from hout.symm ▸ this

    -- arr[left, right] ≤ v → arr'''[left, right] ≤ v
    have : (∀ (k_ : Nat) (_ : k_ < arr.size) (_ : left ≤ k_) (_ : k_ ≤ right), (motive arr[k_]) ) → (∀ (k_ : Nat) (_ : k_ < arr'''.val.size) (_ : left ≤ k_) (_ : k_ ≤ right), (motive arr'''.val[k_])) := (· |> h''1 |> h''2 |> h''3)

    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold qs; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]
  else
    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold qs; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]
termination_by right - left

end qs_monotonic_prelim

set_option maxHeartbeats 5000000 in
theorem qs_monotonic {arr : Array α} {left right : Nat} {hr_size' : right ≤ arr.size.pred} {pivotFactory : PivotFactory α} {q : {a : Array α // a.size = arr.size } } (h : q = qs arr left right hr_size' pivotFactory := by trivial) : ∀ (i_ j_ : Nat) (_ : i_ < q.val.size) (_ : j_ < q.val.size), (left ≤ i_) → (i_ < j_) → (j_ ≤ right) → (q.val[i_] ≤ q.val[j_]) :=

  if hlr : left < right then
    let pivot := pivotFactory _ _ _ hr_size' hlr
    have _ := pivot.hx_left; have _ := pivot.hx_right

    let x := part arr left xhl_size right xhr_size pivot xi_elim xj_elim

    /- termination Proof -/
    have : x.j' < right := part_bounds ‹_› ‹_› |>.right.right
    have _ : x.j' - left < right - left := Nat.sub_lt_sub hlr this

    have : left < x.i' := part_bounds ‹_› ‹_› |>.left.left
    have _ : right - x.i' < right - left := Nat.sub_lt_sub_left hlr this
    /- QED termination Proof -/

    have arr'_property : x.arr'.size = arr.size := part_arr_size

    have : right ≤ x.arr'.size.pred := arr'_property.symm ▸ hr_size'
    have hj_size' : x.j' ≤ x.arr'.size.pred := Nat.le_of_lt (Trans.trans (part_bounds ‹_› ‹_› |>.right.right) this)
    let arr'' := qs x.arr' left x.j' hj_size' pivotFactory
    have h'' : ∀ (i_ j_ : Nat) (_ : i_ < arr''.val.size) (_ : j_ < arr''.val.size), (left ≤ i_) → (i_ < j_) → (j_ ≤ x.j') → (arr''.val[i_] ≤ arr''.val[j_]) := qs_monotonic

    have hr_size'' : right ≤ arr''.val.size.pred := arr''.property.symm ▸ arr'_property.symm ▸ hr_size'
    let arr'''  := qs arr'' x.i' right hr_size'' pivotFactory
    have h''' : ∀ (i_ j_ : Nat) (_ : i_ < arr'''.val.size) (_ : j_ < arr'''.val.size), (x.i' ≤ i_) → (i_ < j_) → (j_ ≤ right) → (arr'''.val[i_] ≤ arr'''.val[j_]) := qs_monotonic

    have hji : x.j' < x.i' := part_j_lt_i

    have : ∀ (i_ j_ : Nat) (_ : i_ < arr'''.val.size) (_ : j_ < arr'''.val.size), left ≤ i_ → i_ < j_ → j_ ≤ right → arr'''.val[i_] ≤ arr'''.val[j_] := fun (i_  j_ : Nat) _ _ (h1 : left ≤ i_) (h2 : i_ < j_) (h3 : j_ ≤ right) =>

      show arr'''.val[i_] ≤ arr'''.val[j_] from
        if hhi : x.i' ≤ i_ then
          by apply h''' <;> assumption
        else if hhj : j_ ≤ x.j' then
          have h'' : ∀ (i_ j_ : Nat) (_ : i_ < arr'''.val.size) (_ : j_ < arr'''.val.size), (left ≤ i_) → (i_ < j_) → (j_ ≤ x.j') → (arr'''.val[i_] ≤ arr'''.val[j_]) := fun i_ j_ _ _ h1 h2 h3 =>
            have _ : j_ < arr''.val.size := arr'''.property ▸ ‹j_ < arr'''.val.size›
            have _ : i_ < arr''.val.size := arr'''.property ▸ ‹i_ < arr'''.val.size›

            have hhhj_ : j_ < x.i' := Trans.trans h3 hji
            have hhhi_ : i_ < x.i' := Trans.trans h2 hhhj_
            have hhhj_: arr''.val[j_] = arr'''.val[j_] := (qs_out_left) j_ ‹_› ‹_› hhhj_ |>.symm
            have hhhi_: arr''.val[i_] = arr'''.val[i_] := (qs_out_left) i_ ‹_› ‹_› hhhi_ |>.symm

            show arr'''.val[i_] ≤ arr'''.val[j_] from hhhj_ ▸ hhhi_ ▸  h'' i_ j_ ‹_› ‹_› h1 h2 h3
          by apply h'' <;> assumption

        else have hhi : i_ < x.i' :=  Nat.gt_of_not_le hhi; have hhj : x.j' < j_ :=  Nat.gt_of_not_le hhj;

          have hhh1 : arr'''.val[i_] ≤ pivot :=
            have _ : i_ < arr''.val.size := arr'''.property ▸ ‹_ < arr'''.val.size›
            have _ : i_ < x.arr'.size := arr''.property ▸ ‹_ < arr''.val.size›

            have : arr''.val[i_] ≤ pivot :=
              if hij'' : i_ ≤ x.j' then
                (qs_invariance (· ≤ pivot.val)) (part_correctness_left) i_ ‹_› h1 hij''
              else have hij'' : x.j' < i_ := Nat.gt_of_not_le hij''
                have : x.arr'[i_] ≤ pivot := (part_correctness_i) i_ ‹_› h1 hhi
                show arr''.val[i_] ≤ pivot from ((qs_out_right) i_ ‹_› ‹_› hij'' |>.symm) ▸ this

            (show arr'''.val[i_] = arr''.val[i_] from (qs_out_left) i_ ‹_› ‹_› hhi).symm ▸ this

          have hhh2 : pivot ≤ arr'''.val[j_] :=
            have _ : j_ < arr''.val.size := arr'''.property ▸ ‹_ < arr'''.val.size›
            have _ : j_ < x.arr'.size := arr''.property ▸ ‹_ < arr''.val.size›

            if hij'' : x.i' ≤ j_ then
              have : ∀ (j_ : Nat) (_ : j_ < arr''.val.size), (x.i' ≤ j_ → j_ ≤ right → pivot ≤ arr''.val[j_]) := fun j_ _ hh1 hh2 =>
                have _ : j_ < x.arr'.size := arr''.property ▸ ‹_ < arr''.val.size›
                have : pivot ≤ x.arr'[j_] := (part_correctness_right) j_ ‹_› hh1 hh2
                show pivot ≤ arr''.val[j_] from  ((qs_out_right) j_ ‹_› ‹_› (Trans.trans hji hh1) |>.symm) ▸ this

              (qs_invariance (pivot.val ≤ ·)) this j_ ‹_› hij'' h3
            else have hij'' : j_ < x.i' := Nat.gt_of_not_le hij''
              have : pivot ≤ x.arr'[j_] := (part_correctness_j) j_ ‹_› hhj h3
              have : pivot ≤ arr''.val[j_] := ((qs_out_right) j_ ‹_› ‹_› hhj |>.symm) ▸ this

              (show arr'''.val[j_] = arr''.val[j_] from (qs_out_left) j_ ‹_› ‹_› hij'').symm ▸ this

          Trans.trans hhh1 hhh2

    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold qs; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]
  else
    have : ∀ (i_ j_ : Nat) (_ : i_ < arr.size) (_ : j_ < arr.size), left ≤ i_ → i_ < j_ → j_ ≤ right → arr[i_] ≤ arr[j_] := fun i_ j_ _ _ h1 h2 h3 => have : left < right := Trans.trans (Trans.trans h1 h2) h3; absurd this hlr
    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold qs; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]
termination_by right - left

set_option maxHeartbeats 200000 in
theorem qs_perm {arr : Array α} {left right : Nat} {hr_size' : right ≤ arr.size.pred} {pivotFactory : PivotFactory α} {q : {a : Array α // a.size = arr.size } } (h : q = qs arr left right hr_size' pivotFactory := by trivial) : arr ~ q :=

  if hlr : left < right then
    let pivot := pivotFactory _ _ _ hr_size' hlr
    have _ := pivot.hx_left; have _ := pivot.hx_right

    let x := part arr left xhl_size right xhr_size pivot xi_elim xj_elim
    have h' : arr ~ x.arr' := part_perm

    /- termination Proof -/
    have : x.j' < right := part_bounds ‹_› ‹_› |>.right.right
    have _ : x.j' - left < right - left := Nat.sub_lt_sub hlr this

    have : left < x.i' := part_bounds ‹_› ‹_› |>.left.left
    have _ : right - x.i' < right - left := Nat.sub_lt_sub_left hlr this
    /- QED termination Proof -/

    have arr'_property : x.arr'.size = arr.size := part_arr_size

    have : right ≤ x.arr'.size.pred := arr'_property.symm ▸ hr_size'
    have hj_size' : x.j' ≤ x.arr'.size.pred := Nat.le_of_lt (Trans.trans (part_bounds ‹_› ‹_› |>.right.right) this)
    let arr'' := qs x.arr' left x.j' hj_size' pivotFactory
    have h'' : x.arr' ~ arr'' := qs_perm

    have hr_size'' : right ≤ arr''.val.size.pred := arr''.property.symm ▸ arr'_property.symm ▸ hr_size'
    let arr'''  := qs arr'' x.i' right hr_size'' pivotFactory
    have h''' : arr'' ~ arr''' := qs_perm

    have _ : arr ~ arr''' := Trans.trans  h' (Trans.trans h'' h''')

    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold qs; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]
  else
    have : arr ~ arr := Array.Perm.refl arr
    by simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]; unfold qs; simp_all [-Nat.not_lt, -not_lt, -Nat.not_le, -not_le]
termination_by right - left

end qs_correct
