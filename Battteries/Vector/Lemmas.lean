
import Batteries.Data.Vector.Lemmas
import Battteries.List.Lemmas

namespace Batteries.Vector

-- -- TODO: (@somombo) add this instance upstream?
-- instance : CoeOut (Vector α n) (Array α) where
--   coe a := a.toArray


-- TODO: @somombo add these to Vectors API
@[simp] theorem getElem_swap_right (a : Vector α n) {i j : Fin n} : (a.swap i j)[j.val] = a[i] := a.1.getElem_swap_right

@[simp] theorem getElem_swap_left (a :  Vector α n) {i j : Fin n} : (a.swap i j)[i.val] = a[j] := a.1.getElem_swap_left

@[simp] theorem getElem_swap_of_ne (a : Vector α n) {i j : Fin n} (hp : p < n)
    (hi : p ≠ i) (hj : p ≠ j) : (a.swap i j)[p] = a[p] := a.1.getElem_swap_of_ne (a.2.symm ▸ hp) hi hj

theorem getElem_swap (a : Vector α n) (i j : Fin n) (k : Nat) (hk : k < n) :
    (a.swap i j)[k] = if k = i then a[j] else if k = j then a[i] else a[k] :=
  a.1.getElem_swap' (i.cast a.2.symm) (j.cast a.2.symm) k (a.2.symm ▸ hk)

@[simp] theorem swap_self (a : Vector α n) {i : Fin n} : a.swap i i = a := by
  apply Vector.ext
  intros; simp only [getElem_swap]
  split <;> simp_all

theorem split_three (as : Vector α n) (h1 : lo ≤ hi) (h2 : hi ≤ n) :
    ∃ (L₁ L₂ L₃ : List α), (L₁.length = lo) ∧ (lo + L₂.length = hi) ∧
      (as.1.toList = L₁ ++ L₂ ++ L₃) :=
  have : hi ≤ as.toArray.size := as.2.symm ▸ h2
  List.exists_three_of_le _ h1 (show hi ≤ as.toArray.toList.length from this)
