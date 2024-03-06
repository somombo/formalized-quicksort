import Std.Data.Array.Lemmas

private theorem fin_cast_val (h : n = n') (i : Fin n) : h ▸ i = ⟨i.1, h ▸ i.2⟩ := by cases h; rfl

namespace Array
attribute [local simp] fin_cast_val

variable {a a': Array α} {i j p: Fin a.size}

theorem swap_def_jeqi : (a.swap i j)[j] = a[i] :=
  by simp [swap]

theorem swap_def_ieqj : (a.swap i j)[i] = a[j] :=
  let vi := a.get i
  let vj := a.get j
  let j := a.size_set i vj ▸ j

  let a := a.set i vj
  let a' := a.set j vi

  suffices a'[i.val] = vj from by simp at this; simp [swap]; assumption
  if he : j.val = i.val then
    by simp [←he]
  else
    suffices a[i.val] = vj from (a.get_set_ne j vi _ he).symm ▸ this
    by simp [get_set_ne]

theorem swap_def_else : i.val≠p.val → j.val≠p.val → (a.swap i j)[p] = a[p] :=
fun hi hj =>
  let vi := a.get i
  let vj := a.get j

  let j' := a.size_set i vj ▸ j
  let a_ := a.set i vj
  let a' := a_.set j' vi

  suffices a'[p.val] = a[p.val] by simp at this; simp [swap]; assumption

  have : j.val=j'.val := by simp
  have h1 : a'[p.val] = a_[p.val] := a_.get_set_ne (j') vi _ (this ▸ hj )
  have h2 : a_[p.val] = a[p.val] := a.get_set_ne i vj _ hi

  trans h1 h2


theorem swap_p : (a.swap i j)[p] = a[if i.val=p.val then j else if j.val=p.val then i else p] :=
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
    apply swap_def_else hi hj

theorem swap_p' : (a.swap i j)[if i.val=p.val then j else if j.val=p.val then i else p] = a[p] :=
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
    apply swap_def_else hi hj

theorem swap_swap_id {a : Array α} (i j : Fin a.size) : a = (a.swap i j).swap (a.size_swap _ _ ▸ i) (a.size_swap _ _ ▸ j) :=
  have hss {a : Array α} {i j : Fin a.size} : a.size = (a.swap i j).size := a.size_swap i j |>.symm
  have hs : a.size = ((a.swap i j).swap (hss ▸ i) (hss ▸ j) ).size := hss ▸ hss

  suffices
    ∀ p_val : Nat,
    (_ : p_val < a.size) →
    (_ : p_val < ((a.swap i j).swap (hss ▸ i) (hss ▸ j) ).size) →
    a[p_val]  = ((a.swap i j).swap (hss ▸ i) (hss ▸ j) )[p_val]
  from Array.ext a ((a.swap i j).swap (hss ▸ i) (hss ▸ j)) hs this

  fun p_val h _ =>
    let p : Fin a.size := ⟨p_val, h⟩
    let p' : Fin (a.swap i j).size := hss ▸ p

    let a' := (swap a i j)
    let i' : Fin a'.size := (hss ▸ i)
    let j' : Fin a'.size := (hss ▸ j)

    have h1 : a[p] = a'[if i.val = p.val then j else if j.val = p.val then i else p] := (@swap_p' _ a i j p |>.symm)

    have h2 : a'[if i.val = p.val then j else if j.val = p.val then i else p] = a'[if i'.val = p'.val then j' else if j'.val = p'.val then i' else p'] := by
      have hi' : i'.val = i.val := by simp
      have hj' : j'.val = j.val := by simp
      have hp' : p'.val = p.val := by simp
      rw [hi', hj', hp']
      split
      . simp
      . split
        . simp
        . simp

    have h3 := (@swap_p _ a' i' j' p' |>.symm)

    have := trans h1 (trans h2 h3)
    by simp at this ; simp ; assumption

theorem swap_comm : a.swap i j = a.swap j i :=
  let a' := a.swap i j
  let a'' := a.swap j i
  suffices a' = a'' from by simp at this; assumption

  have h' : a.size = a'.size := a.size_swap i j |>.symm
  have h'' : a.size = a''.size := a.size_swap j i |>.symm
  have hs : a'.size = a''.size := trans h'.symm h''

  suffices ∀ p_val, (_ : p_val < a'.size) → (_ : p_val < a''.size) → a'[p_val] = a''[p_val] from Array.ext a' a'' hs this

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
  (if i.val=p.val then j else if j.val=p.val then i else p) = (if j.val=p.val then i else if i.val=p.val then j else p) :=
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
