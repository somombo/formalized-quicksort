import Batteries.Data.List.Lemmas

namespace List

-- theorem append_eq_append_iff_of_length_le {a b c d : List α} (h : a.length ≤ c.length) :
--     a ++ b = c ++ d ↔ ∃ a', c = a ++ a' ∧ b = a' ++ d := by
--   refine append_eq_append_iff.trans <| or_iff_left_of_imp ?_
--   rintro ⟨a', rfl, rfl⟩
--   rw [length_append] at h
--   cases length_eq_zero.1 <| Nat.le_zero.1 <| (Nat.add_le_add_iff_left (k := 0)).1 h
--   exact ⟨[], by simp⟩

-- theorem append_eq_append_iff_of_length_le' {a b c d : List α} (h : d.length ≤ b.length) :
--     a ++ b = c ++ d ↔ ∃ a', c = a ++ a' ∧ b = a' ++ d := by
--   refine append_eq_append_iff.trans <| or_iff_left_of_imp ?_
--   rintro ⟨a', rfl, rfl⟩
--   rw [length_append, Nat.add_comm] at h
--   cases length_eq_zero.1 <| Nat.le_zero.1 <| (Nat.add_le_add_iff_left (k := 0)).1 h
--   exact ⟨[], by simp⟩

theorem get_of_append' {l : List α} {n : Fin l.length} (eq : l = l₁ ++ a :: l₂) (h : l₁.length = n.1) :
    l[n] = a := getElem_of_append eq h

theorem exists_of_length_le {n} {l : List α} (h : n ≤ l.length) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ l₁.length = n :=
  ⟨_, _, (take_append_drop n l).symm, length_take_of_le h⟩

theorem exists_of_length_lt {n} {l : List α} (h : n < l.length) :
    ∃ l₁ a l₂, l = l₁ ++ a :: l₂ ∧ l₁.length = n :=
  match exists_of_length_le (Nat.le_of_lt h) with
  | ⟨l₁, [], _, _⟩ => by subst l; simp at h; omega
  | ⟨l₁, a::l₂, H⟩ => ⟨l₁, a, l₂, H⟩

theorem exists_three_of_le (l : List α) (h1 : i ≤ j) (h2 : j ≤ l.length) :
    ∃ l₁ l₂ l₃, l₁.length = i ∧ i + l₂.length = j ∧ l = l₁ ++ l₂ ++ l₃ := by
  obtain ⟨l', l₃, rfl, rfl⟩ := exists_of_length_le h2
  let ⟨l₁, l₂, eq, hl₁⟩ := exists_of_length_le h1
  exact ⟨l₁, l₂, l₃, hl₁, by simp [eq, hl₁]⟩


theorem exists_three_of_lt (l : List α) (h1 : i < j) (h2 : j < l.length) :
    ∃ l₁ a l₂ b l₃, l₁.length = i ∧ i + l₂.length + 1 = j ∧ l = l₁ ++ a :: l₂ ++ b :: l₃ := by
  obtain ⟨l', b, l₃, rfl, rfl⟩ := exists_of_length_lt h2
  let ⟨l₁, a, l₂, eq, hl₁⟩ := exists_of_length_lt h1

  -- exact ⟨l₁, a, l₂, b, l₃, hl₁, by simp [eq, hl₁, Nat.add_succ]⟩
  exact ⟨l₁, a, l₂, b, l₃, hl₁, by simp [eq];  simp only [hl₁, Nat.add_succ]⟩

-- theorem exists_of_get {l : List α} (h : n < l.length) :
--     ∃ l₁ a l₂, l = l₁ ++ a :: l₂ ∧ l₁.length = n ∧ l.get ⟨n, h⟩ = a :=
--   have ⟨_, _, _, eq, hl⟩ := exists_of_length_lt h
--   ⟨_, _, _, eq, hl, get_of_append eq hl⟩

theorem modifyTailIdx_of_append (f : List α → List α) {n} {l : List α}
    (eq : l = l₁ ++ l₂) (h : l₁.length = n) : l.modifyTailIdx f n = l₁ ++ f l₂ :=
  eq ▸ h ▸ modifyTailIdx_add (n := 0) ..

-- #check exists_of_modifyNthTail
-- theorem exists_of_modifyNthTail' (f : List α → List α) {n} {l : List α} (h : n ≤ l.length) :
--     ∃ l₁ l₂, l = l₁ ++ l₂ ∧ l₁.length = n ∧ modifyNthTail f n l = l₁ ++ f l₂ :=
--   have ⟨_, _, eq, hl⟩ := exists_of_length_le h
--   ⟨_, _, eq, hl, modifyNthTail_of_append _ eq hl⟩

theorem modify_of_append (f : α → α) {l : List α} (eq : l = l₁ ++ a :: l₂) (h : l₁.length = n) :
    l.modify f n = l₁ ++ f a :: l₂ := modifyTailIdx_of_append _ eq h

-- #check exists_of_modifyNth
-- theorem exists_of_modifyNth' (f : α → α) {n} {l : List α} (h : n < l.length) :
--     ∃ l₁ a l₂, l = l₁ ++ a :: l₂ ∧ l₁.length = n ∧ modifyNth f n l = l₁ ++ f a :: l₂ :=
--   have ⟨_, _, _, eq, hl⟩ := exists_of_length_lt h
--   ⟨_, _, _, eq, hl, modifyNth_of_append _ eq hl⟩

theorem set_of_append {l : List α} (a') (eq : l = l₁ ++ a :: l₂) (h : l₁.length = n) :
    l.set n a' = l₁ ++ a' :: l₂ := by rw [set_eq_modify]; exact modify_of_append _ eq h

-- @somombo TODO: added this extra
theorem perm_mem_getElem {l1 l2 : List α} (h : l1 ~ l2) : ∀ (i : Fin l1.length), ∃ (j : Fin l2.length), l2[j] = l1[i] := by
  intro i
  have : _ ↔ ∃ (j : Fin l2.length), l2[j] = l1[i] := l2.mem_iff_get
  simp only [←this]
  simp only [←h.mem_iff]
  apply l1.get_mem
