
import Bench.Basic


def main (args : List String): IO Unit := do
  let some arg := args[0]? | throw <| IO.userError s!"specify size test array"
  let some size := arg.toNat? | throw <| IO.userError s!"specify size test array"

  let unique_ratio := 0.00002
  let swaps_ratio := 1
  let reverse := false
  let _ ← make_input size (unique_ratio := unique_ratio) (swaps_ratio := swaps_ratio) (reverse := reverse)
  println! s!"Done Generating data with (size := {size}) (unique_ratio := {unique_ratio}) (swaps_ratio := {swaps_ratio})"
-- --------------
