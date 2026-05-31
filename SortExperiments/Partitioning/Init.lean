
module

@[specialize]
public structure Partitioning (α: Type u) (n : Nat)  where
  arr' : Vector α n
  j' : Nat
  i' : Nat
  deriving Repr, Nonempty, Inhabited





-- @[simp, grind .]
-- theorem dbgTraceIfShared_noop : (dbgTraceIfShared s a) = a := rfl
