module

public import SortExperiments.Pivot.Init

/-

```lean4
-- in `SortExperiments.Pivot.Init`
@[specialize]
public structure Pivot (α: Type u) (n : Nat)  where
  piv' : α
  arr' : Vector α n
  deriving Repr, Nonempty, Inhabited
```
-/

@[inline]
private def Vector.insertionSortAt {n : Nat} (xs : Vector α n) (getIdxAt : Fin (M + 1) → Fin n /- := by exact Fin.castLE (by grind) -/)
    [Ord α] : Vector α n :=
  traverse xs 1
where
  @[specialize]
  traverse (xs : Vector α n) (i : Nat)  : Vector α n :=
    if h : i ≤ M then
      traverse (swapLoop xs i (by omega)) (i+1)
    else
      xs
    termination_by M + 1 - i

  @[specialize]
  swapLoop (xs : Vector α n) (j : Nat) (h : j ≤ M) :  Vector α n :=
    if h0j : 0 < j then
      let j' := j - 1
      let ⟨j'_, hj'⟩ := getIdxAt ⟨j', by omega⟩
      let ⟨j_, hj⟩ := getIdxAt ⟨j, by omega⟩
      if compare xs[j_] xs[j'_] |>.isLT then
        swapLoop (xs.swap j_ j'_) j' (by grind)
      else
        xs
    else
      xs





private theorem Nat.percentile_lower {left : Nat} {right : Nat} {M : Nat} (hlr : left < right) :
    ∀ {p : Fin (M + 1)}, (left*M + p.val * (right - left)) ≤ M*right := by
  intro p
  have _ : p * (right - left) ≤ M * (right - left) := Nat.mul_le_mul_right _ (by omega)
  have _ : M * (right - left) = M * right - M * left := Nat.mul_sub_left_distrib ..
  have _ : M * left ≤ M * right := Nat.mul_le_mul_left _ (by omega)
  have _ : left * M = M * left := Nat.mul_comm ..
  omega




private def sample_idxs {n : Nat} {left right : Nat} (hlr : left < right) (hr : right < n) (M : Nat) (p : Fin (M + 1)) :
  Fin n := ⟨(left * M + p * (right - left)) / M, by
    have := Nat.div_le_of_le_mul (Nat.percentile_lower (p := p) hlr)
    grind
  ⟩



@[inline]
public def Pivot.median (M : Nat) [Ord α] (arr : Vector α n) (left : Nat)  (right : Nat) (hlr : left < right) (hr : right < n) : Pivot α n:=
  have hl : left < n := by omega

  let idxFn := sample_idxs hlr hr M
  let idxVec  := Vector.ofFn idxFn
  let arr_ := arr.insertionSortAt idxVec.get

  let mid  := idxFn ⟨M/2, by omega⟩
  let pivot := arr_[mid]
  ⟨pivot, arr_⟩


-- open Ord in
public theorem Pivot.median_sorted [Ord α] {M : Nat} (hM : M > 0)
    (not_lt : ∀ {x y : α}, ¬(compare y x |>.isLT) ↔ (compare x y |>.isLE) := by grind)
    (le_trans : ∀ {x y z : α}, (compare x y).isLE → (compare y z).isLE → (compare x z).isLE := by grind)
    {arr : Vector α n} {left right: Nat} (hlr : left < right) (hr : right < n) :
    let ⟨pivot, arr_⟩ := Pivot.median M arr left right hlr hr;
    ¬(compare pivot arr_[left] |>.isLT) ∧ ¬(compare arr_[right] pivot |>.isLT) := by
  sorry


-------------------------------------------------

def left := 0
def right := 100
def M := 32






example {m n k : Nat} : m ≤ k * n → m / k ≤ n := Nat.div_le_of_le_mul
example {n m k : Nat} (hk : 0 < k) (h : n * k ≤ m) : n ≤ (m / k) := (Nat.le_div_iff_mul_le hk).mpr h
example {left : Nat} {right : Nat} {M : Nat} /- (hlr : left < right)  -/: M*left ≤ (left*M + p*(right - left))  := by grind

-- import Quicksort.Init.Ord
-- import Std.Data.Iterators
-- #eval (0...=M).iter.map (fun p => left + ((p * (right - left))/M)) |>.toArray
-- #eval (0...=M).iter.map (fun p => (left*M + p*(right - left))/M ) |>.toArray -- Seems more correct but may be computationally unecessary
