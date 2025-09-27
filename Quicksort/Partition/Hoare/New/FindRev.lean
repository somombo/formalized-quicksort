



variable {α : Type u}

def Array.findIdxRev.loop (p : α → Bool) (as : Array α)
    (j : Fin as.size) (h : ∃ (j' : Fin as.size), j' ≤ j.val ∧ p as[j']) : Fin as.size :=
  if _ : p as[j] then
    j
  else
    Array.findIdxRev.loop p as ⟨j - 1, by grind [Nat.pred_le]⟩ (by grind)
termination_by j.val
decreasing_by grind

@[grind]
def Array.findIdxRev.loop! (p : α → Bool) (as : Array α)
    (j : Fin as.size) : Fin as.size :=
  if _ : p as[j] then
    j
  else
    Array.findIdxRev.loop! p as ⟨j - 1, by grind [Nat.pred_le]⟩
partial_fixpoint



  -- unfold hoare.classic.loop.while_j'


/-
Defines a possibly non-terminating function as a fixed-point in a suitable partial order.

Such a function is compiled as if it was marked partial, but its equations are provided as theorems, so that it can be verified.

In general it accepts functions whose return type has a Lean.Order.CCPO instance and whose definition is Lean.Order.monotone with regard to its recursive calls.

Common special cases are

Functions whose type is inhabited a-priori (as with partial), and where all recursive calls are in tail-call position.
Monadic in certain “monotone chain-complete monads” (in particular, Option) composed using the bind operator and other supported monadic combinators.
By default, the monotonicity proof is performed by the compositional monotonicity tactic. Using the syntax partial_fixpoint monotonicity by $tac the proof can be done manually.
-/

theorem Array.findIdxRev.loop_part_eq_tot {p : α → Bool} {as : Array α}
    {j : Fin as.size} (h : ∃ (j' : Fin as.size), j' ≤ j.val ∧ p as[j']) :
    Array.findIdxRev.loop! p as j = Array.findIdxRev.loop p as j h := by
  fun_induction Array.findIdxRev.loop <;> grind



namespace Vector
variable {α : Type u} (p : α → Bool) (as : Vector α n)

#check Array.findIdx
-- #check Vector.findIdx

def findIdxRev.loop' (j : Fin n) : Fin n :=
  if _ : p as[j] then
    j
  else
    findIdxRev.loop' ⟨j - 1, by grind⟩
termination_by j.val
decreasing_by
  -- have h : ∃ (j' : Fin n), j' ≤ j.val ∧ p as[j'] := sorry
  have _ := j.2
  have h : p as[0] := sorry
  grind



def findIdxRev.loop (j : Fin n) (h : ∃ (j' : Fin n), j' ≤ j.val ∧ p as[j']) : Fin n :=
  if _ : p as[j] then
    j
  else
    findIdxRev.loop ⟨j - 1, by grind⟩ (by grind)
termination_by j.val
decreasing_by grind



@[grind]
def findIdxRev.loop! (j : Fin n) : Fin n :=
  if _ : p as[j] then
    j
  else
    findIdxRev.loop! ⟨j - 1, by grind⟩
partial_fixpoint

theorem findIdxRev.loop_part_eq_tot {p : α → Bool} {as : Vector α n}
    {j : Fin n} (h : ∃ (j' : Fin n), j' ≤ j.val ∧ p as[j']) :
    findIdxRev.loop! p as j = Vector.findIdxRev.loop p as j h := by
  fun_induction findIdxRev.loop <;> grind
end Vector

open Vector
