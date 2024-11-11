
import Batteries.Data.Vector.Basic

open Batteries


structure Partition (α: Type u) (n : Nat)  where
  arr' : Vector α n
  j' : Nat
  i' : Nat
  -- deriving Repr

variable [Ord α]
-- variable (lt : α → α → Bool)

abbrev lt (x y : α) : Bool :=
  match compare x y with
  | .lt => true
  | _ => false

def sortAt (as : Vector α n) (low high : Nat) (hlh : low ≤ high) (hn : high < n) : Vector α n :=
  if _ : lt as[high] as[low] then
    as.swap ⟨low, by omega⟩ ⟨high, by assumption⟩
  else
    as

abbrev PartitioningAlgorithm α :=  {n : Nat} → Vector α n → (left right : Nat) → left < right → right < n →  { x : Partition α n  // left < x.i' ∧ x.j' < right }




@[inline] def hoare.partition [Ord α] {n : Nat} (arr : Vector α n) (left : Nat)  (right : Nat) (hlr : left < right) (hr : right < n) : {x : Partition α n // (left < x.i') ∧ (x.j' < right)} :=
  let mid := left + ((right - left)/2)
  let arr_ := arr
    |> (sortAt · left mid (by omega) (by omega))
    |> (sortAt · left right (by omega) (by omega))
    |> (sortAt · mid right (by omega) (by omega))
  have pivot := arr_[mid]

  let rec @[specialize] loop (arr : Vector α n) (i j : Nat) (hli : left < i) (hjr : j < right) (hij : i ≤ j + 1) : { x : Partition α n // left < x.i' ∧ x.j' < right } :=
    if _ : j < i then
      ⟨⟨arr, j, i⟩, ⟨hli, hjr⟩⟩
    else
      if _ : (lt arr[i] pivot)  then
        loop arr (i + 1) j (by omega) (by omega) (by omega)
      else if _ : (lt pivot arr[j]) then
        loop arr i (j - 1) (by omega) (by omega) (by omega)
      else
        if hlt : i < j then
          loop (arr.swap ⟨i, by omega⟩ ⟨j, by omega⟩) (i + 1) (j - 1) (by omega) (by omega) (by omega)
        else
          ⟨⟨arr, j - 1, i + 1⟩, ⟨(by omega : _ < i + 1), (by omega : j - 1 < _)⟩⟩
  -- termination_by j + 1 - i

  loop arr_ (left + 1) (right - 1) (by omega) (by omega) (by omega)



@[inline] def lomuto.partition [Ord α] {n : Nat} (arr : Vector α n) (left : Nat)  (right : Nat) (hlr : left < right) (hr : right < n) : {x : Partition α n // (left < x.i') ∧ (x.j' < right)} :=
  let mid := left + ((right - left)/2)
  let arr_ := arr
    |> (sortAt · left mid (by omega) (by omega))
    |> (sortAt · left right (by omega) (by omega))
    |> (sortAt · mid right (by omega) (by omega))
  have pivot := arr_[right]

  let rec @[specialize] loop (as : Vector α n) (i j : Nat) (hli : left < i) (hij :  i ≤ j  ) (hjr : j ≤ right) : { x : Partition α n // left < x.i' ∧ x.j' < right } :=
    let i_fin : Fin n := ⟨i, by omega⟩

    if _ : j < right then
      if _ : lt as[j] pivot then
        loop (as.swap i_fin ⟨j, by omega⟩) (i + 1) (j + 1) (by omega) (by omega) (by omega)
      else
        loop as i (j + 1) hli (by omega) (by omega)
    else
      ⟨⟨as.swap i_fin ⟨right, hr⟩, i - 1, i + 1⟩, by simp only; omega, by simp only; omega⟩
  -- termination_by right - j
  loop arr_ (left + 1) (left + 1) (by omega) (by omega) (by omega)



instance [Ord α] : Inhabited (PartitioningAlgorithm α) := ⟨hoare.partition⟩
instance [Ord α] : Inhabited (PartitioningAlgorithm α) := ⟨lomuto.partition⟩



 @[inline] def qs [Ord α] (arr : Array α) (left : Nat := 0) (right : Nat := arr.size - 1) (part : PartitioningAlgorithm α := @default _ _) : Array α :=
  let rec @[specialize] strict {n : Nat} (as : Vector α n) (left : Nat := 0) (right : Nat := n - 1) (hsize' : right ≤ n - 1) : Batteries.Vector α n :=
    if hlr : left < right then
      let ⟨⟨as', j', i'⟩, ⟨(_ : _ < i'), (_ : j' < _ )⟩⟩ := part as left right hlr (by omega)
      let as := qs.strict as' left j' (by omega)
      let as := qs.strict as i' right (by omega)
      as
    else
      as
    termination_by right - left

  let right' : Nat := if right ≤ arr.size - 1 then right else
    have := Inhabited.mk (arr.size - 1)
    panic! "index out of bounds"

  have : right' ≤ arr.size - 1 := by
    simp [right']; split <;> simp [panicWithPosWithDecl, panic, panicCore, *]

  qs.strict ⟨arr, rfl⟩ left right' this |>.1
