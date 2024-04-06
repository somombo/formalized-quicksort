import Std.Data.Array.Lemmas

section subst_lemmas
section comm
@[simp] private theorem fin_cast_val_comm (h1 : n = n' := by first | trivial | simp_all) (h2 : n' = n'' := by first | trivial | simp_all) (i : Fin n) : ((h1 ▸ h2 : n = n'') ▸ i : Fin n'')  =  (h2 ▸ (h1 ▸ i) : Fin n'') := by cases h1; rfl
@[simp] private theorem prod_fin_cast_val_comm (h1 : n = n' := by first | trivial | simp_all) (h2 : n' = n'' := by first | trivial | simp_all) (p : Fin n × Fin n) : ((h1 ▸ h2 : n = n'') ▸ p : Fin n'' × Fin n'')  =  (h2 ▸ (h1 ▸ p) : Fin n'' × Fin n'') := by cases h1; rfl

@[simp] private theorem list_prod_fin_cast_val_comm (h1 : n = n' := by first | trivial | simp_all) (h2 : n' = n'' := by first | trivial | simp_all) (ps: List (Fin n × Fin n)) : ((h1.symm ▸ h2 : n = n'') ▸ ps : List (Fin n'' × Fin n''))  =  (h2 ▸ (h1 ▸ ps) : List (Fin n'' × Fin n'')) := by cases h1; rfl

end comm

@[simp] private theorem gen_cast_val_inverse {motive : Nat → Sort u} (h : n = n' := by first | trivial | simp_all)  (x : motive n) : h.symm ▸ h ▸ x = x := by cases h; rfl

@[simp] private theorem fin_cast_val (h : n = n' := by first | trivial | simp_all) (i : Fin n) : h ▸ i = ⟨i.1, h ▸ i.2⟩ := by cases h; rfl


@[simp] private theorem prod_fin_cast_val (h : n = n' := by first | trivial | simp_all) (p : Fin n × Fin n) : h ▸ p = (h ▸ p.1, h ▸ p.2) := by cases h; rfl


@[simp] private theorem list_prod_fin_cast_val (h : n = n' := by first | trivial | simp_all) (ps : List (Fin n × Fin n)) : h ▸ ps = ps.map (fun p => ⟨⟨p.1.1, h ▸ p.1.2⟩, ⟨p.2.1, h ▸ p.2.2⟩⟩) :=
  have aux : h ▸ ps = ps.map (h ▸ ·) := by cases h; simp -- ; apply Eq.symm; induction ps <;> simp_all
  by simp_all

@[simp] private theorem list_prod_fin_cast_val_append (h : n = n' := by first | trivial | simp_all) (ps ps': List (Fin n × Fin n)) : h ▸ (ps ++ ps') =  (h ▸ ps) ++ (h ▸ ps') := by simp_all


@[simp] private theorem list_prod_fin_cast_val_reverse {ps : List (Fin n × Fin n)} (h : n = n' := by first | trivial | simp_all) : h ▸ (ps.reverse) = (h ▸ ps).reverse := by cases h; rfl


end subst_lemmas


namespace Array

variable {a a': Array α} {i j p: Fin a.size}

@[simp] def swaps (a : Array α) : List (Fin a.size × Fin a.size) → Array α
  | [] => a
  | (i, j) :: ijs =>
    have : (a.swap i j).size = a.size := a.size_swap _ _

    -- swaps (a.swap i j) (this.symm ▸ ijs)
    swaps (a.swap i j) (ijs.map (fun p => ⟨⟨p.1.1, this.symm ▸ p.1.2⟩, ⟨p.2.1, this.symm ▸ p.2.2⟩⟩))
termination_by l => l.length



@[simp] theorem swaps_zero_eq_swap : a.swaps [] = a := by simp
@[simp] theorem swaps_one_eq_swap : a.swaps [(i, j)] = a.swap i j := by simp
@[simp] theorem swaps_two_eq_swap_swap {i1 j1 i2 j2 : Fin a.size}: a.swaps [(i1, j1),(i2, j2)] = (a.swap i1 j1).swap (⟨i2.1, (a.size_swap _ _).symm ▸ i2.2⟩) ⟨j2.1, (a.size_swap _ _).symm ▸ j2.2⟩ :=  by simp

@[simp] theorem swaps_two_id : a.swaps [c,c]  = a := by let (i, j) := c; simp


@[simp] theorem size_swaps (a : Array α) : ∀ {l}, (a.swaps l).size = a.size
  | [] => by simp
  | (i, j) :: ijs => trans (size_swaps (a.swap i j) ..) (a.size_swap _ _)
termination_by l => l.length


@[simp] theorem swaps_append (a : Array α) (l l': List (Fin a.size × Fin a.size)) : (a.swaps l).swaps (a.size_swaps.symm ▸ l') = a.swaps (l ++ l') :=
  match l with
  | [] =>
    suffices swaps (swaps a []) l' = swaps a l' by simp_all
    have : a.swaps [] = a :=  a.swaps_zero_eq_swap
    congrArg (fun _ => swaps a l') this

  | (i, j) :: ijs =>
    have hs : (a.swap i j).size = a.size := a.size_swap _ _
    have hs's: ((a.swap i j).swaps (hs.symm ▸ ijs)).size = (a.swap i j).size := (a.swap i j).size_swaps
    have hss : ((a.swap i j).swaps (hs.symm ▸ ijs)).size = a.size := hs's.symm ▸ hs

    have ih : ((a.swap i j).swaps (hs.symm ▸ ijs)).swaps (hs's.symm ▸ (hs.symm ▸ l')) = (a.swap i j).swaps ((hs.symm ▸ ijs) ++ (hs.symm ▸ l')) := swaps_append (a.swap i j) (hs.symm ▸ ijs) (hs.symm ▸ l')

    have h_suff : ((a.swap i j).swaps (hs.symm ▸ ijs)).swaps (hss.symm ▸ l') = (a.swap i j).swaps (hs.symm ▸ (ijs ++ l')) :=
      (list_prod_fin_cast_val_comm (hs.symm) (hs's.symm) (l')).symm ▸ ((list_prod_fin_cast_val_append hs.symm (ijs) (l')).symm ▸ ih)

    have : (a.swaps ((i, j) :: ijs)) = ((a.swap i j).swaps (hs.symm ▸ ijs)) := by simp
    have : {val := (a.swaps ((i, j) :: ijs)), property := a.size_swaps.symm : Subtype (a.size = ·.size)} = {val := ((a.swap i j).swaps (hs.symm ▸ ijs)), property := hss.symm : Subtype (a.size = ·.size)} := Subtype.eq this

    have heq : (a.swaps ((i, j) :: ijs)).swaps (a.size_swaps.symm ▸ l') = ((a.swap i j).swaps (hs.symm ▸ ijs)).swaps (hss.symm ▸ l') := congrArg (fun x => swaps x.1 (x.2 ▸ l')) this

      show (a.swaps ((i, j) :: ijs)).swaps (a.size_swaps.symm ▸ l') = a.swaps ((i, j) :: ijs ++ l') by simp_all
  termination_by l.length

set_option maxHeartbeats 5000000 in
@[simp] theorem swaps_cancel (a : Array α) (l : List (Fin a.size × Fin a.size)) : a.swaps (l ++ l.reverse) = a :=
  match l with
  | [] => by simp

  | c :: cs =>

    have hs' : (a.swaps [c]).size = a.size := a.size_swaps

    have hs'' : ((a.swaps [c]).swaps (hs'.symm ▸ (cs ++ cs.reverse))).size = (a.swaps [c]).size := (a.swaps [c]).size_swaps
    have hs : ((a.swaps [c]).swaps (hs'.symm ▸ (cs ++ cs.reverse))).size = a.size :=  hs''.symm ▸ hs'

    have : ((a.swaps [c]).swaps ((hs'.symm ▸ cs) ++ (hs'.symm ▸ cs).reverse)) = (a.swaps [c]) := swaps_cancel (a.swaps [c]) (hs'.symm ▸ cs)
    have : ((a.swaps [c]).swaps ((hs'.symm ▸ cs) ++ (hs'.symm ▸ cs.reverse))) = (a.swaps [c]) := (list_prod_fin_cast_val_reverse hs'.symm) ▸ this
    have ih : ((a.swaps [c]).swaps (hs'.symm ▸ (cs ++ cs.reverse))) = (a.swaps [c]) := (list_prod_fin_cast_val_append hs'.symm .. ▸ this)

    have heq_comm : (hs.symm ▸ [c] : List (Fin ((a.swaps [c]).swaps (hs'.symm ▸ (cs ++ cs.reverse))).size × Fin ((a.swaps [c]).swaps (hs'.symm ▸ (cs ++ cs.reverse))).size))  =  (hs''.symm ▸ (hs'.symm ▸ [c]) : List (Fin ((a.swaps [c]).swaps (hs'.symm ▸ (cs ++ cs.reverse))).size × Fin ((a.swaps [c]).swaps (hs'.symm ▸ (cs ++ cs.reverse))).size)) :=  (list_prod_fin_cast_val_comm hs'.symm hs''.symm) [c]

    calc  a.swaps ((c :: cs) ++ (c :: cs).reverse)
      _ = a.swaps (      [c] ++ (cs ++ cs.reverse ++ [c])     ) := by simp
      _ = (a.swaps [c]).swaps ( hs'.symm ▸ (cs ++ cs.reverse ++ [c]) ) := (swaps_append a [c] (cs ++ cs.reverse ++ [c])).symm
      _ = (a.swaps [c]).swaps ( (hs'.symm ▸ (cs ++ cs.reverse)) ++ (hs'.symm ▸ [c]) ) := by simp
      _ = ((a.swaps [c]).swaps (hs'.symm ▸ (cs ++ cs.reverse))).swaps  (hs''.symm ▸ (hs'.symm ▸ [c])) := (swaps_append (a.swaps [c])  (hs'.symm ▸ (cs ++ cs.reverse)) (hs'.symm ▸ [c])).symm
      _ = ((a.swaps [c]).swaps (hs'.symm ▸ (cs ++ cs.reverse))).swaps  (hs.symm ▸ [c]) := by rw [←heq_comm]
      _ = (a.swaps [c]).swaps  (hs'.symm ▸ [c]) := by congr ; simp
      _ = a.swaps ([c] ++ [c]) := swaps_append a [c] [c]
      _ = a := swaps_two_id

  termination_by l.length


@[simp] def Perm (a a' : Array α) := ∃ (l : List (Fin a.size × Fin a.size)), a' = a.swaps l

/-
  Defines notation for "a 'is a permutation of' b".
  FIXME: `(priority := high)` is currently set in order to (potentially) override
  incompatible definition found in Mathlib.Data.List.Perm
  The ideal solution would be for the ~ symbol to be defined by a type class
  that can accommodate different variations of the definition of permutation
  (e.g. as a bijection)
-/
infixl:50 (priority := high) " ~ " => Perm

namespace Perm
variable {a1 a2 a3 : Array α}

theorem size_eq (h : a1 ~ a2) : a1.size = a2.size := by cases h ; simp_all

theorem refl : ∀ a : Array α, a ~ a := fun _ => ⟨[], by simp⟩
theorem of_eq (h : a1 = a2) : a1 ~ a2 := h ▸ refl a1


theorem symm (h : a1 ~ a2) : a2 ~ a1 :=
  have hs : a1.size = a2.size := h.size_eq

  let ⟨l, h⟩ := h; -- have h : a2 = (a1.swaps l) := h

  have : ⟨a2, hs⟩ = {val := (a1.swaps l), property := h ▸ hs : Subtype (a1.size = ·.size)} := Subtype.eq h

  have : a2.swaps ((h.symm ▸ a1.size_swaps) ▸ l.reverse) = a1 :=
    calc a2.swaps ((h.symm ▸ a1.size_swaps) ▸ l.reverse)
      _ = (a1.swaps l).swaps (a1.size_swaps ▸ l.reverse) := congrArg (fun x => swaps x.1 (x.2 ▸ l.reverse)) this
      _ = a1.swaps (l ++ l.reverse) := swaps_append a1 l l.reverse
      _ = a1 := swaps_cancel a1 l
  ⟨(h.symm ▸ a1.size_swaps) ▸ l.reverse, this.symm⟩


theorem trans (h1 : a1 ~ a2) (h2 : a2 ~ a3) : a1 ~ a3 :=
  let swaps_append_gen  (a : Array α) {n n' : Nat} {l : List (Fin n × Fin n)} {l' : List (Fin n' × Fin n')} (hn : n = a.size) (h : n' = n) (hn' : n' = (a.swaps (hn ▸ l)).size) : (a.swaps (hn ▸ l)).swaps (hn' ▸ l') = a.swaps ((hn ▸ l) ++ ((h.symm ▸ hn) ▸ l')) :=
    let swaps_append_short (a : Array α) (l : List (Fin a.size × Fin a.size)) (l': List (Fin (a.swaps l).size × Fin (a.swaps l).size)) : (a.swaps l).swaps l' = a.swaps (l ++ (a.size_swaps ▸ l')) :=
      have _ : a.size_swaps.symm ▸ a.size_swaps ▸ l' = l' := gen_cast_val_inverse (motive := (fun n => List (Fin n × Fin n))) ..
      have _ : (a.swaps l).swaps (a.size_swaps.symm ▸ a.size_swaps ▸ l') = a.swaps (l ++ (a.size_swaps ▸ l')) := swaps_append a l (a.size_swaps ▸ l')
      by simp_all

    have hss : (a.swaps (hn ▸ l)).size = a.size := Trans.trans (Trans.trans hn'.symm h) hn
    have : (a.swaps (hn ▸ l)).swaps (hn' ▸ l') = a.swaps ((hn ▸ l) ++ (hss ▸ hn' ▸ l')) := swaps_append_short a (hn ▸ l) (hn' ▸ l')

    have _ : (h.symm ▸ hn) ▸ l' = hss ▸ (hn' ▸ l') := (list_prod_fin_cast_val_comm) l'
    by simp_all

  ------------------

  let ⟨l1, h1'⟩ := h1; -- have h1' : a2 = a1.swaps l1 := h1'
  let ⟨l2, h2'⟩ := h2; -- have h2' : a3 = a2.swaps l2 := h2'

  have hs1 : a1.size = (a1.swaps l1).size := (a1.size_swaps).symm
  have hs2 : a2.size = a1.size := h1'.symm ▸ a1.size_swaps
  have hs3 : a2.size = (a1.swaps l1).size := Trans.trans hs2 hs1

  have h3' : a3 = (a1.swaps l1).swaps ((Trans.trans hs2 hs1) ▸ l2) := h1' ▸ h2'
  have : (a1.swaps l1).swaps (hs3 ▸ l2) = a1.swaps (l1 ++ (hs2 ▸ l2)) := swaps_append_gen a1 rfl hs2 .. /- hs3 -/

  have : a3 = a1.swaps (l1 ++ (hs2 ▸ l2)) := Trans.trans h3'  this

  ⟨l1 ++ (hs2 ▸ l2), this⟩



instance : Trans (. ~ . : Array α → Array α → Prop) (. ~ . : Array α → Array α → Prop) (. ~ . : Array α → Array α → Prop) where
  trans := Array.Perm.trans

theorem equivalence (α) : Equivalence (@Perm α) := ⟨Perm.refl, Perm.symm, Perm.trans⟩
instance isSetoid (α) : Setoid (Array α) := ⟨(@Perm α), (Perm.equivalence α)⟩


end Perm
