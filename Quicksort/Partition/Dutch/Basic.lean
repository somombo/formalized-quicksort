import Quicksort.Partition.Init.Basic

open Batteries Vector

/-
  imperetive implimentation of Three-Way "Dutch National Flag" Partition
 -/
-- def dutch.example [Ord α] {n : Nat} (as : Vector α n) (left : Nat)  (right : Nat) (hlr : left < right) (hr : right < n) : {x : Partition α n // (left < x.i') ∧ (x.j' < right)} := Id.run do
--   let mid := left + ((right - left)/2)
--   have _ : left < n := by omega
--   have _ : right < n := hr
--   have _ : mid < n := by omega
--   -- Pivot value
--   let pivot := as[mid] -- Choose the middle element as the pivot (integer division)

--   -- Lesser, equal and greater index
--   let mut (as, i, k, j) := (as, left + 1, left + 1, right - 1)
--   -- -- Iterate and compare all elements with the pivot

--   while k ≤ j do
--     if lt (as.get ⟨k, sorry⟩) pivot then
--       -- Swap the elements at the equal and lesser indices
--       as := as.swap ⟨k, sorry⟩ ⟨i, sorry⟩
--       -- Increase lesser index
--       i := i + 1
--       -- Increase equal index
--       k := k + 1
--     else if lt pivot (as.get ⟨k, sorry⟩) then
--       -- Swap the elements at the equal and greater indices
--       as := as.swap ⟨k, sorry⟩ ⟨j, sorry⟩
--       -- Decrease greater index
--       j := j - 1
--       -- k := k + 1
--     else  -- if arr[k] = pivot then
--       -- Increase equal index
--       k := k + 1
--   return ⟨⟨as, i - 1, j + 1⟩, by simp only; sorry, by simp only; sorry⟩

-- #eval! dutch.example #v[9,  3,  1,  8,  6,  2,  5,  -0,  7,  4]  0 9 (by omega) (by omega)
-- -- { arr' := { toArray := #[4, 3, 1, 0, 2, 5, 6, 7, 8, 9], size_eq := _ }, j' := 5, i' := 7 }

/--
  Three-Way "Dutch National Flag" Partitioning Scheme
 -/
@[inline]
def Partition.dutch [Ord α] {n : Nat} (as : Vector α n) (left : Nat)  (right : Nat) (hlr : left < right) (hr : right < n) : {x : Partition α n // (left < x.i') ∧ (x.j' < right)} :=
  let mid := left + ((right - left)/2)
  have hl : left < n := by omega
  have hm : mid < n := by omega
  let as_ := as
    |> (maybeSwap · ⟨left, hl⟩ ⟨mid, hm⟩)
    |> (maybeSwap · ⟨left, hl⟩ ⟨right, hr⟩)
    |> (maybeSwap · ⟨mid, hm⟩ ⟨right, hr⟩)

  let pivot := as_[mid] -- Choose the median-of-three element as the pivot

  -- Iterate and compare all elements with the pivot
  let rec loop (as : Vector α n) (i k j : Nat) (hli : left < i) (hik : i ≤ k ) (hjr : j < right) (hlj : left ≤ j) (hir : i ≤  right ) : {x : Partition α n // (left < x.i') ∧ (x.j' < right)} :=
    if hkj : k ≤ j then
      have hk : k < n := by omega
      if lt as[k] pivot then
        by apply loop (as.swap ⟨k, hk⟩ ⟨i, by omega⟩) (i + 1) (k + 1) j; all_goals omega
      else if lt pivot as[k] then
        by apply loop (as.swap ⟨k, hk⟩ ⟨j, by omega⟩) i k (j - 1); all_goals omega
      else
        by apply loop as i (k + 1) j; all_goals omega
    else
      ⟨⟨as, i - 1, j + 1⟩, by simp only; omega, by simp only; omega⟩
  termination_by j + n - i - k

  by apply loop as_ (left + 1) (left + 1) (right - 1); all_goals omega

-- #eval Partition.dutch #v[3, 1, 3] 0 2 (by omega) (by omega)
/--
  Three-Way "Dutch National Flag" Partitioning Scheme
 -/
@[inline]
def Partition.dutch_both [Ord α] {n : Nat} (as : Vector α n) (left : Nat)  (right : Nat) (hlr : left < right) (hr : right < n) : {x : Partition α n // (left < x.i') ∧ (x.j' < right)} :=
  let mid := left + ((right - left)/2)
  have hl : left < n := by omega
  have hm : mid < n := by omega
  let as_ := as
    |> (maybeSwap · ⟨left, hl⟩ ⟨mid, hm⟩)
    |> (maybeSwap · ⟨left, hl⟩ ⟨right, hr⟩)
    |> (maybeSwap · ⟨mid, hm⟩ ⟨right, hr⟩)

  let pivot := as_[mid] -- Choose the median-of-three element as the pivot

  -- Iterate and compare all elements with the pivot
  let rec loop (as : Vector α n) (i i_ j j_ : Nat) (hli : left < i) (hik : i ≤ i_ ) /- (hij : i ≤  j + 1) -/ (hik : j_ ≤ j ) (hjr : j < right) (hlj : left ≤ j) (hir : i ≤  right ) : {x : Partition α n // (left < x.i') ∧ (x.j' < right)} :=
    if hkj : i_ ≤ j_  then
      have hi_ : i_ < n := by omega
      have hj_ : j_ < n := by omega
      if lt as[i_] pivot then
        by apply loop (as.swap ⟨i_, hi_⟩ ⟨i, by omega⟩) (i + 1) (i_ + 1) j j_; all_goals omega
      else if lt pivot as[j_] then
        by apply loop (as.swap ⟨j_, hj_⟩ ⟨j, by omega⟩) i i_ (j - 1) (j_ - 1); all_goals omega
      else
        by apply loop as i (i_ + 1) j (j_ - 1); all_goals omega
    else
      ⟨⟨as, j_ , i_⟩, by simp only; omega, by simp only; omega⟩
  -- termination_by j_ + 1  - i_


  by apply loop as_ (left + 1) (left + 1) (right - 1) (right - 1); all_goals omega

-- #eval Partition.dutch #v[3, 1, 3] 0 2 (by omega) (by omega)
#eval Partition.dutch_both #v[9,  3,  1,  8,  6,  2,  5,  -0,  7,  4]  0 9 (by omega) (by omega)
-- -- { arr' := { toArray := #[4, 3, 1, 0, 2, 5, 6, 7, 8, 9], size_eq := _ }, j' := 5, i' := 7 }
