import Quicksort.Partition.Init.Basic

open Batteries Vector
def dbg {α : Type u} [ToString α] (s : String) (a : α)  : α :=
  dbgTrace s!"{s}" (fun _ => a)

instance [ToString α] : ToString (Vector α n) where
  toString a := s!"#v{a.toList}"
/-
  imperetive implimentation of Single Pivot yaroslavskiy partitioning scheme
 -/
def Partition.yaroslavskiy.example [Ord α] [ToString α]  {n : Nat} (as_ : Vector α n) (left : Nat)  (right : Nat) (hlr : left < right) (hr : right < n) : {x : Partition α n // (left < x.i') ∧ (x.j' < right)} :=
  let mid := left + ((right - left)/2)
  have hl : left < n := by omega
  have hm : mid < n := by omega
  let as_ := as_
    |> (maybeSwap · ⟨left, hl⟩ ⟨mid, hm⟩)
    |> (maybeSwap · ⟨left, hl⟩ ⟨right, hr⟩)
    |> (maybeSwap · ⟨mid, hm⟩ ⟨right, hr⟩)


  -- Pivot value --   pivot := as_[left]; pivot := as_[right]
  let pivot := as_[mid] -- Choose the middle element as the pivot (integer division)
  let pivot := dbg s!"pivot {pivot}" pivot

  let as_ := dbg s!"as_: {as_}" as_
  -- if pivot > pivot then Swap pivot and pivot end if
  let rec outer_while_loop (as : Vector α n) (i k j : Nat): (Vector α n) × Nat × Nat := Id.run do
    let mut (as, i, k, j) := (as, i, k, j)
    while k ≤ j do
      if lt (as.get ⟨k, sorry⟩) pivot then
        as := as.swap ⟨k, sorry⟩ ⟨i, sorry⟩
        i := i + 1
        k := k + 1
      else
        -- while (lt pivot (as.get ⟨j, sorry⟩))  ∧ (k < j) do
        --   j := dbg s!"before({k}): (a[{j}] := {(as.get ⟨j, sorry⟩)} > {pivot} = {(lt pivot (as.get ⟨j, sorry⟩))}) && ({k} < {j} = {decide (k < j)})" j
        --   j := j - 1
        -- j := dbg s!"after({k}): (a[{j}] := {(as.get ⟨j, sorry⟩)} > {pivot} = {(lt pivot (as.get ⟨j, sorry⟩))}) && ({k} < {j} = {decide (k < j)})" j

          -- j := dbg s!"newj {k}" (j - 1)



        -- if ¬lt pivot (as.get ⟨k, sorry⟩) then
        --   k := k + 1
        -- else
        as := as.swap ⟨k, sorry⟩ ⟨j, sorry⟩
        j := j - 1
        -- k := k + 1

        -- if lt pivot (as.get ⟨k, sorry⟩) then
        --   as := as.swap ⟨k, sorry⟩ ⟨j, sorry⟩
        --   j := j - 1
        -- else
        --   k := k + 1
    return (as, i, j)


  let (as_, i_, j_) := outer_while_loop (as := as_) (i := left + 1) (k := left + 1) (j := right - 1)
  -- let i_ := i_ - 1
  -- let j_ := j_ + 1
  -- let as_ := as_.swap ⟨i_, sorry⟩ ⟨left, sorry⟩
  -- let as_ := as_.swap ⟨j_, sorry⟩ ⟨right, sorry⟩
  ⟨⟨as_, i_ - 1, j_ + 1⟩, by simp only; sorry, by simp only; sorry⟩


-- #eval! Partition.yaroslavskiy.example #v[3, 4, 2, 1]  0 3 (by omega) (by omega)

#eval! Partition.yaroslavskiy.example #v[0, 1]  0 1 (by omega) (by omega)
#eval! Partition.yaroslavskiy.example #v[1, 0]  0 1 (by omega) (by omega)
#eval! Partition.yaroslavskiy.example #v[2, 1, 3]  0 2 (by omega) (by omega)
#eval! Partition.yaroslavskiy.example #v[1, 2, 3]  0 2 (by omega) (by omega)

-- #eval! Partition.yaroslavskiy.example #v[3, 4, 2, 1]  0 3 (by omega) (by omega)
#eval! Partition.yaroslavskiy.example #v[9,  3,  1,  8,  6,  2,  5,  0,  7,  4]  0 9 (by omega) (by omega)
#eval! Partition.yaroslavskiy.example #v[4, 9,  3,  1,  8,  6,  2, 0,  7,  4]  0 9 (by omega) (by omega)
-- { arr' := { toArray := #[4, 3, 1, 0, 2, 5, 6, 7, 8, 9], size_eq := _ }, j' := 5, i' := 7 }

/-
  imperetive implimentation of Single Pivot yaroslavskiy partitioning scheme
 -/
def Partition.yaroslavskiy.debug [Ord α] [ToString α]  {n : Nat} (as : Vector α n) (left : Nat)  (right : Nat) (hlr : left < right) (hr : right < n) : {x : Partition α n // (left < x.i') ∧ (x.j' < right)} := Id.run do
  let mid := left + ((right - left)/2)
  let mut as := as
    |> (maybeSwap · ⟨left, by omega⟩ ⟨mid, by omega⟩)
    |> (maybeSwap · ⟨left, by omega⟩ ⟨right, by omega⟩)
    |> (maybeSwap · ⟨mid, by omega⟩ ⟨right, by omega⟩)
    -- |> (maybeSwap · ⟨right, by omega⟩ ⟨mid, by omega⟩)

  let pivot := as[mid]
  -- let pivot := as[left]
  let pivot := dbg s!"pivot: {pivot}" pivot
  -- let pivot' := as[right]
  -- let pivot' := dbg s!"pivot': {pivot'}" pivot'

  let mut (i, k, j) := (left + 1, left + 1, right - 1)
  as := dbg s!"as0: {as}  i={i}  k={k}  j={j}" as
  while k ≤ j do
    if lt (as.get ⟨k, sorry⟩) pivot then
      as := as.swap ⟨k, sorry⟩ ⟨i, sorry⟩
      -- if k ≠ i then as := dbg s!"as_: {as}  i={i}  k={k}  j={j}" as
      i := i + 1
    else -- if (¬lt (as.get ⟨k, sorry⟩) pivot) then
      while (lt pivot (as.get ⟨j, sorry⟩))  ∧ (k < j) do  -- A[j] > pivR AND k < j
        j := j - 1
      as := as.swap ⟨k, sorry⟩ ⟨j, sorry⟩
      j := j - 1
      -- if k ≠ j then as := (dbg s!"as_: {as}  i={i}  k={k}  j={j}" as)
      if lt (as.get ⟨k, sorry⟩) pivot then
        as := as.swap ⟨k, sorry⟩ ⟨i, sorry⟩
        -- if k ≠ i then as := dbg s!"as_: {as}  i={i}  k={k}  j={j}" as
        i := i + 1

    k := k + 1

  -- i := i - 1
  -- as := as.swap ⟨left, sorry⟩ ⟨i, sorry⟩
  -- j := j + 1
  -- as := as.swap ⟨right, sorry⟩ ⟨j, sorry⟩
  -- if k = j then j := j - 1

  -- i := i + 1
  -- j := j - 1
  -- as := as.swap ⟨right, sorry⟩ ⟨i, sorry⟩
  as := dbg s!"i={i}  k={k}  j={j}" as
  ⟨⟨as, j, i⟩, by simp only; sorry, by simp only; sorry⟩
/-
  imperetive implimentation of Single Pivot yaroslavskiy partitioning scheme
 -/
def Partition.yaroslavskiy.debug_func [Ord α] [ToString α]  {n : Nat} (as : Vector α n) (left : Nat)  (right : Nat) (hlr : left < right) (hr : right < n) : {x : Partition α n // (left < x.i') ∧ (x.j' < right)} := Id.run do
  let mid := left + ((right - left)/2)
  let mut as := as
    |> (maybeSwap · ⟨left, by omega⟩ ⟨mid, by omega⟩)
    |> (maybeSwap · ⟨left, by omega⟩ ⟨right, by omega⟩)
    |> (maybeSwap · ⟨mid, by omega⟩ ⟨right, by omega⟩)
    -- |> (maybeSwap · ⟨right, by omega⟩ ⟨mid, by omega⟩)

  let pivot := as[mid]
  -- let pivot := as[left]
  let pivot := dbg s!"pivot: {pivot}" pivot
  -- let pivot' := as[right]
  -- let pivot' := dbg s!"pivot': {pivot'}" pivot'

  let mut (i, k, j) := (left + 1, left + 1, right - 1)
  as := dbg s!"as0: {as}  i={i}  k={k}  j={j}" as
  while k ≤ j do
    if lt (as.get ⟨k, sorry⟩) pivot then
      as := as.swap ⟨k, sorry⟩ ⟨i, sorry⟩
      -- if k ≠ i then as := dbg s!"as_: {as}  i={i}  k={k}  j={j}" as
      i := i + 1
      k := k + 1
    else -- if (¬lt (as.get ⟨k, sorry⟩) pivot) then
      while (lt pivot (as.get ⟨j, sorry⟩))  ∧ (k < j) do  -- A[j] > pivR AND k < j
        j := j - 1
      -- as := (as.swap ⟨k, sorry⟩ ⟨j, sorry⟩)
      -- if k ≠ j then as := (dbg s!"as_: {as}  i={i}  k={k}  j={j}" as)
      if lt (as.get ⟨j, sorry⟩) pivot then
        as := (as.swap ⟨k, sorry⟩ ⟨j, sorry⟩).swap ⟨k, sorry⟩ ⟨i, sorry⟩
        -- if k ≠ i then as := dbg s!"as_: {as}  i={i}  k={k}  j={j}" as
        j := j - 1
        k := k + 1
        i := i + 1
      else
        j := j - 1
        k := k + 1

  -- i := i - 1
  -- as := as.swap ⟨left, sorry⟩ ⟨i, sorry⟩
  -- j := j + 1
  -- as := as.swap ⟨right, sorry⟩ ⟨j, sorry⟩
  -- if k = j then j := j - 1

  -- i := i + 1
  -- j := j - 1
  -- as := as.swap ⟨right, sorry⟩ ⟨i, sorry⟩
  as := dbg s!"i={i}  k={k}  j={j}" as
  ⟨⟨as, j, i⟩, by simp only; sorry, by simp only; sorry⟩

#eval! Partition.yaroslavskiy.debug #v[0, 1]  0 1 (by omega) (by omega)
#eval! Partition.yaroslavskiy.debug #v[1, 0]  0 1 (by omega) (by omega)
#eval! Partition.yaroslavskiy.debug #v[2, 1, 3]  0 2 (by omega) (by omega)
#eval! Partition.yaroslavskiy.debug #v[1, 2, 3]  0 2 (by omega) (by omega)

-- #eval! Partition.yaroslavskiy.debug #v[3, 4, 2, 1]  0 3 (by omega) (by omega)
#eval! Partition.yaroslavskiy.debug #v[9,  3,  1,  8,  6,  2,  5,  0,  7,  4]  0 9 (by omega) (by omega)
#eval! Partition.yaroslavskiy.debug #v[4, 9,  3,  1,  8,  6,  2, 0,  7,  4]  0 9 (by omega) (by omega)
-- { arr' := { toArray := #[4, 3, 1, 0, 2, 5, 6, 7, 8, 9], size_eq := _ }, j' := 5, i' := 7 }











/-
  imperetive declarative of Single Pivot yaroslavskiy partitioning scheme
 -/
def Partition.yaroslavskiy.debug' [Ord α] [ToString α]  {n : Nat} (as : Vector α n) (left : Nat)  (right : Nat) (hlr : left < right) (hr : right < n) : {x : Partition α n // (left < x.i') ∧ (x.j' < right)} := Id.run do
  let mid := left + ((right - left)/2)
  let mut as_ := as
    |> (maybeSwap · ⟨left, by omega⟩ ⟨mid, by omega⟩)
    |> (maybeSwap · ⟨left, by omega⟩ ⟨right, by omega⟩)
    |> (maybeSwap · ⟨mid, by omega⟩ ⟨right, by omega⟩)
    -- |> (maybeSwap · ⟨right, by omega⟩ ⟨mid, by omega⟩)

  let pivot := as_[mid]
  let pivot := dbg s!"pivot: {pivot}" pivot

  let rec loop (as : Vector α n) (i k j : Nat) : {x : Partition α n // (left < x.i') ∧ (x.j' < right)} :=
    if  (lt pivot (as.get ⟨j, sorry⟩))  ∧ (k < j) then
      loop as i k (j - 1)
    else
      if k ≤ j then
        if lt (as.get ⟨j, sorry⟩) pivot then
          loop ((as.swap ⟨k, sorry⟩ ⟨j, sorry⟩).swap ⟨k, sorry⟩ ⟨i, sorry⟩) (i + 1) (k + 1) (j - 1)
        else
        loop as i (k + 1) (j - 1)
      else
        let as := dbg s!"k: {k}" as
        ⟨⟨as, j, i⟩, by simp only; sorry, by simp only; sorry⟩

        -- sorry

    termination_by j + 1 - k

  loop as_ (left + 1) (left + 1) (right - 1)




#eval! Partition.yaroslavskiy.debug' #v[0, 1]  0 1 (by omega) (by omega)
#eval! Partition.yaroslavskiy.debug' #v[1, 0]  0 1 (by omega) (by omega)
#eval! Partition.yaroslavskiy.debug' #v[2, 1, 3]  0 2 (by omega) (by omega)
#eval! Partition.yaroslavskiy.debug' #v[1, 2, 3]  0 2 (by omega) (by omega)
#eval! Partition.yaroslavskiy.debug' #v[3, 4, 2, 1]  0 3 (by omega) (by omega)
#eval! Partition.yaroslavskiy.debug' #v[9,  3,  1,  8,  6,  2,  5,  0,  7,  4]  0 9 (by omega) (by omega)
#eval! Partition.yaroslavskiy.debug' #v[4, 9,  3,  1,  8,  6,  2, 0,  7,  4]  0 9 (by omega) (by omega)
-- { arr' := { toArray := #[4, 3, 1, 0, 2, 5, 6, 7, 8, 9], size_eq := _ }, j' := 5, i' := 7 }












-- /--
--   Single Pivot yaroslavskiy partitioning scheme
--  -/
-- @[inline]
-- def Partition.yaroslavskiy [Ord α] {n : Nat} (as : Vector α n) (left : Nat)  (right : Nat) (hlr : left < right) (hr : right < n) : {x : Partition α n // (left < x.i') ∧ (x.j' < right)} :=
--   let mid := left + ((right - left)/2)
--   have hl : left < n := by omega
--   have hm : mid < n := by omega
--   let as_ := as
--     |> (maybeSwap · ⟨left, hl⟩ ⟨mid, hm⟩)
--     |> (maybeSwap · ⟨left, hl⟩ ⟨right, hr⟩)
--     |> (maybeSwap · ⟨mid, hm⟩ ⟨right, hr⟩)

--   let pivot := as_[mid] -- Choose the median-of-three element as the pivot

--   -- Iterate and compare all elements with the pivot
--   let rec loop (as : Vector α n) (i k j : Nat) (hli : left < i) (hik : i ≤ k ) (hjr : j < right) (hlj : left ≤ j) (hir : i ≤  right ) : {x : Partition α n // (left < x.i') ∧ (x.j' < right)} :=
--     if hkj : k ≤ j then
--       have hk : k < n := by omega
--       if lt as[k] pivot then
--         by apply loop (as.swap ⟨k, hk⟩ ⟨i, by omega⟩) (i + 1) (k + 1) j; all_goals omega
--       else if lt pivot as[k] then
--         by apply loop (as.swap ⟨k, hk⟩ ⟨j, by omega⟩) i k (j - 1); all_goals omega
--       else
--         by apply loop as i (k + 1) j; all_goals omega
--     else
--       ⟨⟨as, i - 1, j + 1⟩, by simp only; omega, by simp only; omega⟩
--   termination_by j + n - i - k

--   by apply loop as_ (left + 1) (left + 1) (right - 1); all_goals omega

-- -- #eval Partition.yaroslavskiy #v[3, 1, 3] 0 2 (by omega) (by omega)
