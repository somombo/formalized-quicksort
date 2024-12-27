
import Batteries.Data.Vector.Basic
import Battteries.Vector.Lemmas

open Batteries

abbrev lt [Ord α] (x y : α) : Bool :=
  match compare x y with
  | .lt => true
  | _ => false

def Batteries.Vector.maybeSwap [Ord α] (as : Vector α n) (low high : Fin n) : Vector α n :=
  if lt as[high] as[low] then
    as.swap low high
  else
    as


structure Partition (α: Type u) (n : Nat)  where
  arr' : Vector α n
  j' : Nat
  i' : Nat
  deriving Repr

abbrev Partition.Scheme α :=  [Ord α] → {n : Nat} → Vector α n → (left right : Nat) → left < right → right < n →  { x : Partition α n  // left < x.i' ∧ x.j' < right }
