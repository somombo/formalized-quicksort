
-- import Batteries.Data.Vector.Lemmas
-- import Battteries.List.Lemmas

private theorem List.exists_three_of_le (l : List α) (h1 : i ≤ j) (h2 : j ≤ l.length) :
    ∃ l₁ l₂ l₃, l₁.length = i ∧ i + l₂.length = j ∧ l = l₁ ++ l₂ ++ l₃ := by

  let exists_of_length_le {n} {l : List α} (h : n ≤ l.length) :
      ∃ l₁ l₂, l = l₁ ++ l₂ ∧ l₁.length = n :=
    ⟨_, _, (List.take_append_drop n l).symm, List.length_take_of_le h⟩

  obtain ⟨l', l₃, rfl, rfl⟩ := exists_of_length_le h2
  let ⟨l₁, l₂, eq, hl₁⟩ := exists_of_length_le h1
  exact ⟨l₁, l₂, l₃, hl₁, by simp [eq, hl₁]⟩


theorem Vector.split_three (as : Vector α n) (h1 : lo ≤ hi) (h2 : hi ≤ n) :
    ∃ (L₁ L₂ L₃ : List α), (L₁.length = lo) ∧ (lo + L₂.length = hi) ∧
      (as.1.toList = L₁ ++ L₂ ++ L₃) :=
  have : hi ≤ as.toArray.size := as.2.symm ▸ h2
  List.exists_three_of_le _ h1 (show hi ≤ as.toArray.toList.length from this)


-- #check Vector



-- namespace Vector

-- -- TODO: (@somombo) add this instance upstream?
-- instance : CoeOut (Vector α n) (Array α) where
--   coe a := a.toArray


-- TODO: @somombo add these to Vectors API
#check _root_.Vector.getElem_swap_of_ne
-- @[simp] theorem getElem_swap_right (a : Vector α n) {i j : Fin n} : (a.swap i j)[j.val] = a[i] := a.1.getElem_swap_right

-- @[simp] theorem getElem_swap_left (a :  Vector α n) {i j : Fin n} : (a.swap i j)[i.val] = a[j] := a.1.getElem_swap_left

-- @[simp] theorem getElem_swap_of_ne (a : Vector α n) {i j : Fin n} (hp : p < n)
--     (hi : p ≠ i) (hj : p ≠ j) : (a.swap i j)[p] = a[p] := a.1.getElem_swap_of_ne (a.2.symm ▸ hp) hi hj


#check Vector.getElem_swap

-- @[grind]
-- theorem getElem_swap'' {xs : Vector α n} {i j : Nat} (hi hj) {k : Nat} (hk : k < n) :
--     (xs.swap i j hi hj)[k] = if k = i then xs[j] else if k = j then xs[i] else xs[k] := by
--   cases xs
--   simp_all [Array.getElem_swap]


-- theorem getElem_swap (a : Vector α n) (i j : Fin n) (k : Nat) (hk : k < n) :
--     (a.swap i j)[k] = if k = i then a[j] else if k = j then a[i] else a[k] :=
--   a.1.getElem_swap' (i.cast a.2.symm) (j.cast a.2.symm) k (a.2.symm ▸ hk)
-- end Vector
