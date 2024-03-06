import Mathlib.Init.Data.Int.Order
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Data.String.Basic
--------------------------------------
-- import Quicksort.Order.Defs

-- import Std.Data.Int.Order

-- instance : LinearOrder Int where
--   le_refl : ∀ a : Int, a ≤ a := Int.le_refl
--   le_trans : ∀ a b c : Int, a ≤ b → b ≤ c → a ≤ c := @Int.le_trans
--   lt_iff_le_not_le : ∀ a b : Int, a < b ↔ a ≤ b ∧ ¬b ≤ a := @Int.lt_iff_le_not_le
--   le_antisymm : ∀ a b : Int, a ≤ b → b ≤ a → a = b := @Int.le_antisymm
--   le_total (a b : Int) : a ≤ b ∨ b ≤ a := Int.le_total ..
--   decidableLE : DecidableRel (· ≤ · : Int → Int → Prop) := Int.decLe
