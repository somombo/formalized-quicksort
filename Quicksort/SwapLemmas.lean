import Std.Data.Array.Lemmas
/-!
See https://github.com/leanprover/std4/pull/688
-/

private theorem fin_cast_val (h : n = n') (i : Fin n) : h ▸ i = ⟨i.1, h ▸ i.2⟩ := by cases h; rfl
namespace Array

/-! ### swap -/

@[simp] theorem swap_def_jeqi {a: Array α} {i j : Nat}
    (_ : i < a.size := by trivial) (_ : j < a.size := by trivial)
    (_ : j < (a.swap ⟨i, ‹_›⟩ ⟨j, ‹_›⟩).size := by trivial) : (a.swap ⟨i, _⟩ ⟨j, _⟩)[j] = a[i] :=
  let i : Fin a.size := ⟨i, _⟩
  let j : Fin a.size := ⟨j, _⟩

  show (a.swap i j)[j] = a[i] from aux
where aux {i j : Fin a.size} : (a.swap i j)[j] = a[i] := by simp [swap, fin_cast_val]

@[simp] theorem swap_def_ieqj {a: Array α} {i j : Nat}
    (_ : i < a.size := by trivial) (_ : j < a.size := by trivial)
    (_ : i < (a.swap ⟨i, ‹_›⟩ ⟨j, ‹_›⟩).size := by trivial) : (a.swap ⟨i, _⟩ ⟨j, _⟩)[i] = a[j] :=
  let i : Fin a.size := ⟨i, _⟩
  let j : Fin a.size := ⟨j, _⟩

  show (a.swap i j)[i] = a[j] from aux
where aux {i j : Fin a.size} : (a.swap i j)[i] = a[j] :=
  let vi := a.get i
  let vj := a.get j
  let j := a.size_set i vj ▸ j

  let a := a.set i vj
  let a' := a.set j vi

  suffices a'[i.val]/- '(by simp [a, a']) -/ = vj from by simp [a'] at this; assumption
  if he : j.val = i.val then
    by simp [←he, vi, vj, j, a', fin_cast_val]
  else
    suffices a[i.val]/- '(by simp [a]) -/ = vj from (a.get_set_ne j vi _ he).symm ▸ this
    by simp [get_set_ne, a]

@[simp] theorem swap_def_else {a: Array α} {i j : Fin a.size}
    (_ : p < a.size := by trivial) (_ : p < (a.swap i j).size := by trivial)
    (_ : i.val ≠ p) (_ : j.val ≠ p) : (a.swap i j)[p] = a[p] :=
  let i : Fin a.size := ⟨i, _⟩
  let j : Fin a.size := ⟨j, _⟩
  let p : Fin a.size := ⟨p, ‹_›⟩

  show (a.swap i j)[p] = a[p] by apply aux <;> simp_all only [ne_eq, not_false_eq_true]
where aux {i j p: Fin a.size} (hi : i.val ≠ p.val) (hj : j.val ≠ p.val) : (a.swap i j)[p] = a[p] :=
  let vi := a.get i
  let vj := a.get j

  let j' := a.size_set i vj ▸ j
  let a_ := a.set i vj
  let a' := a_.set j' vi

  suffices a'[p.val]/- '(by simp [a_, a']) -/ = a[p.val] by simp [a'] at this; assumption

  have : j.val=j'.val := by simp [j', fin_cast_val]
  have h1 : a'[p.val]/- '(by simp [a', a_]) -/ = a_[p.val]/- '(by simp [a_]) -/ :=
    a_.get_set_ne (j') vi _ (this ▸ hj )
  have h2 : a_[p.val]/- '(by simp [a_]) -/ = a[p.val] := a.get_set_ne i vj _ hi

  trans h1 h2


theorem swap_p {a: Array α} {i j p : Fin a.size} :
    (a.swap i j)[p] = a[if i.val=p.val then j else if j.val=p.val then i else p] :=
  if hi : i.val=p.val then by
    simp [←hi]
    apply swap_def_ieqj
  else if hj : j.val=p.val then by
    simp [hi]
    simp [←hj]
    apply swap_def_jeqi
  else by
    simp [hi]
    simp [hj]
    apply swap_def_else <;> assumption

theorem swap_p' {a: Array α} {i j p : Fin a.size} :
    (a.swap i j)[if i.val=p.val then j else if j.val=p.val then i else p] = a[p] :=
  if hi : i.val=p.val then by
    simp [←hi]
    apply swap_def_jeqi
  else if hj : j.val=p.val then by
    simp [hi]
    simp [←hj]
    apply swap_def_ieqj
  else by
    simp [hi]
    simp [hj]
    apply swap_def_else <;> assumption

@[simp] theorem swap_swap_id {a: Array α} {i j : Fin a.size} :
    (a.swap i j).swap (a.size_swap _ _ ▸ i) (a.size_swap _ _ ▸ j) = a :=
  have hss {a : Array α} {i j : Fin a.size} : a.size = (a.swap i j).size := (a.size_swap i j).symm
  have hs : a.size = ((a.swap i j).swap (hss ▸ i) (hss ▸ j) ).size := hss ▸ hss

  suffices
    ∀ p_val : Nat,
    (_ : p_val < ((a.swap i j).swap (hss ▸ i) (hss ▸ j) ).size) →
    (_ : p_val < a.size) →
    ((a.swap i j).swap (hss ▸ i) (hss ▸ j) )[p_val]  = a[p_val]
  from Array.ext ((a.swap i j).swap (hss ▸ i) (hss ▸ j)) a hs.symm this

  fun p_val _ h =>
    let p : Fin a.size := ⟨p_val, h⟩
    let p' : Fin (a.swap i j).size := hss ▸ p

    let a' := (swap a i j)
    let i' : Fin a'.size := (hss ▸ i)
    let j' : Fin a'.size := (hss ▸ j)

    have h1 : a[p] = a'[if i.val = p.val then j else if j.val = p.val then i else p]/- '(by simp [a']) -/
      := @swap_p' _ a i j p |>.symm

    have h2 : a'[if i.val = p.val then j else if j.val = p.val then i else p]/- '(by simp [a']) -/
        = a'[if i'.val = p'.val then j' else if j'.val = p'.val then i' else p'] := by

      have hi' : i'.val = i.val := by simp [i', fin_cast_val]
      have hj' : j'.val = j.val := by simp [j', fin_cast_val]
      have hp' : p'.val = p.val := by simp [p', fin_cast_val]
      rw [hi', hj', hp']
      split
      . simp [j', fin_cast_val]
      . split
        . simp [i', fin_cast_val]
        . simp [p', fin_cast_val]

    have h3 := @swap_p _ a' i' j' p' |>.symm

    have : (swap a' i' j')[p'] = a[p] := trans h1 (trans h2 h3) |>.symm
    by simp [i', j', p'] at this ; simp_all only [size_swap, getElem_fin, fin_cast_val]

theorem swap_comm {a: Array α} {i j : Fin a.size} : a.swap i j = a.swap j i :=
  let a' := a.swap i j
  let a'' := a.swap j i
  suffices a' = a'' from by simp [a', a''] at this; assumption

  have h' : a.size = a'.size := a.size_swap i j |>.symm
  have h'' : a.size = a''.size := a.size_swap j i |>.symm
  have hs : a'.size = a''.size := trans h'.symm h''

  suffices ∀ p_val, (_ : p_val < a'.size) → (_ : p_val < a''.size) → a'[p_val] = a''[p_val] from
    Array.ext a' a'' hs this

  fun p_val hle' _ =>
    let p : Fin a.size := ⟨p_val, h'.symm ▸ hle'⟩
    let p' := if i.val=p.val then j else if j.val=p.val then i else p
    let p'' := if j.val=p.val then i else if i.val=p.val then j else p

    have hidx : p' = p'' := hidx_aux i j p

    have hh1' : a'[p] = a[p'] := swap_p
    have hh2' : a'[p] = a[p''] := by simp [←hidx]; assumption
    have hh1'' : a[p''] = a''[p] := swap_p.symm

    show a'[p] = a''[p] from trans hh2' hh1''

where hidx_aux (i j p : _) :
  (if i.val=p.val then j else if j.val=p.val then i else p) =
  (if j.val=p.val then i else if i.val=p.val then j else p) :=
    if hi : i.val=p.val then
      if hj : j.val=p.val then by
        simp_all [←hi, ←hj]
        apply (Fin.eq_of_val_eq hj)
      else if hi : i.val=p.val then by
        simp_all
      else by
        simp_all
    else if _ : j.val=p.val then
      if _ : j=p then by
        simp_all
      else if _ : i.val=p.val then by
        simp_all
      else by
        simp_all
    else
      if _ : j.val=p.val then by
        simp_all
      else if hip' : i.val=p.val then by
        simp_all
      else by
        simp_all
