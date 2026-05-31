module


@[specialize]
public structure Pivot (α: Type u) (n : Nat)  where
  piv' : α
  arr' : Vector α n
  deriving Repr, Nonempty, Inhabited
