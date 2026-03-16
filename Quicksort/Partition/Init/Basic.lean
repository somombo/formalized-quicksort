-- def lt (lt : α → α → Bool := by exact (· < ·)) (x y : α) : Bool :=
--   match compare x y with
--   | .lt => true
--   | _ => false

-- abbrev lt [Ord α] (x y : α) := compare x y |>.isLT

def Vector.maybeSwap (lt : α → α → Bool := by exact (· < ·)) (as : Vector α n) (low high : Fin n) : Vector α n :=
  if lt as[high] as[low] then
    as.swap low high
  else
    as


structure Partition (α: Type u) (n : Nat)  where
  arr' : Vector α n
  j' : Nat
  i' : Nat
  deriving Repr, Nonempty, Inhabited

abbrev Partition.Scheme α :=  {n : Nat} → Vector α n → (left right : Nat) → left < right → right < n → (lt : α → α → Bool := by exact (· < ·)) →  { x : Partition α n  // left < x.i' ∧ x.j' < right }

-- private def dbg {α : Type u} [ToString α] (a : α) (s : String)  : α :=
--   dbgTrace s!"{s}" (fun _ => a)

-- private instance [ToString α] : ToString (Vector α n) where
--   toString v := s!"#v{v.toList}"
