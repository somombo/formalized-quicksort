import Batteries.Data.Vector.Basic
import Batteries.Data.Vector.Lemmas
import Battteries.Array.Perm
import Battteries.Vector.Lemmas

/--
The notation typeclass for heterogeneous permutations.
This enables the notation `a ~ b : γ` where `a : α`, `b : β`.
-/
class HPerm (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hPerm : α → β → γ

/-- The homogeneous version of `HPerm`: `a ~ b : Prop` where `a b : α`. -/
class _root_.Perm (α : Type u) where
  /-- `a ~ b` ascerts that  `a` is a permutation of `b`. See `HPerm`. -/
  perm : α → α → Prop

@[default_instance]
instance instHPerm [Perm α] : HPerm α α Prop where
  hPerm a b := Perm.perm a b

infix:50 " ~ "  => HPerm.hPerm

namespace List
instance instListPerm (α : Type u) : _root_.Perm (List α)  where
  perm x y := x ~ y
end List

namespace Array
instance instArrayPerm (α : Type u) : Perm (Array α)  where
  perm x y := x.toList ~ y.toList
end Array

namespace Batteries.Vector
instance instVectorPerm {n : Nat} (α : Type u) : Perm (Vector α n)  where
  perm x y := x.toArray ~ y.toArray
end Batteries.Vector

private theorem List.getElem_append_left'' {l₁ l₂ : List α} {n : Nat} (h : n < l₁.length) : (l₁ ++ l₂)[n]'(by simp; omega) = l₁[n] := List.getElem_append_left ..
private theorem List.getElem_append_right'' {l₁ l₂ : List α} {n : Nat} (h : n < l₂.length) : (l₁ ++ l₂)[l₁.length + n]'(by simp; omega) = l₂[n] := by
  simp only [List.getElem_append_right' l₁ h, Nat.add_comm]

namespace Batteries.Vector
/-- `PermStabilizing left right as₁ as₂` asserts that `as₁` and `as₂` are permutations of each other,
and moreover they agree outside the range `left..=right`. -/
def PermStabilizing' (left right : Nat) (as₁ as₂ : Vector α n) :=
  as₁ ~ as₂ ∧ (∀ i : Fin n, i < left → as₁[i] = as₂[i]) ∧ (∀ j : Fin n, right < j → as₁[j] = as₂[j])

@[refl]
protected theorem PermStabilizing'.refl (as : Vector α n) :
    PermStabilizing' left right as as := ⟨.refl _, fun _ _ => .refl _, fun _ _ => .refl _⟩

protected theorem PermStabilizing'.symm
    (h : PermStabilizing' left right as₁ as₂) :
    PermStabilizing' left right as₂ as₁ where
  left := h.1.symm
  right.left _  := (h.2.1 _ · |>.symm)
  right.right _  := (h.2.2 _ · |>.symm)

protected theorem PermStabilizing'.trans
    (h1 : PermStabilizing' left right as₁ as₂) (h2 : PermStabilizing' left right as₂ as₃) :
    PermStabilizing' left right as₁ as₃ where
  left := h1.1.trans h2.1
  right.left _ hi := (h1.2.1 _ hi).trans (h2.2.1 _ hi)
  right.right _ hj := (h1.2.2 _ hj).trans (h2.2.2 _ hj)

protected theorem PermStabilizing'.mono (h : PermStabilizing' left right as₁ as₂)
    (hleft : left' ≤ left) (hright : right ≤ right') : PermStabilizing' left' right' as₁ as₂ where
  left := h.1
  right.left _ hi := h.2.1 _ <| Nat.lt_of_lt_of_le hi hleft
  right.right _ hj := h.2.2 _ <| Nat.lt_of_le_of_lt hright hj


theorem swap_permStabilizing' {as : Vector α n} {i j : Fin n} {left right : Nat}
    (h_i1 : left ≤ i) (h_i2 : i ≤ right) (h_j1 : left ≤ j) (h_j2 : j ≤ right) :
    PermStabilizing' left right (as.swap i j) as := by
  refine ⟨Array.swap_perm .., fun k hk => ?_, fun k hk => ?_⟩
  repeat
  · simp [Vector.getElem_swap]
    split
    · omega
    · split
      · omega
      · rfl

private theorem PermStabilizing'.mem_getElem {n left hi : Nat} {as as' : Vector α n}
    (hperm : PermStabilizing' left (hi - 1) as as') (hr' : hi ≤ n) :
    ∀ (i : Fin n) (_ : left ≤ i) (_ : i < hi), ∃ (j : Fin n) (_ : left ≤ j) (_ : j < hi), as'[j] = as[i] :=
  fun i hli hir => if _ : hi = 0 then by omega else

  have hlr' : left ≤ hi := by omega

  -- h₁ : L₁.length = left
  -- h₂ : left + L₂.length = hi
  -- h₃ : as.toArray.toList = L₁ ++ L₂ ++ L₃
  have ⟨L₁, L₂, L₃, h₁, h₂, h₃⟩ := Batteries.Vector.split_three as hlr' hr'
  have ⟨L₁', L₂', L₃', h₁', h₂', h₃'⟩ := Batteries.Vector.split_three as' hlr' hr'

  have hasn : as.toArray.toList.length = n := by simp only [as.2]
  have hlll : (L₁ ++ L₂ ++ L₃).length = n := by rwa [←h₃]
  have hasn': as'.toArray.toList.length = n := by simp only [as'.2]
  have hlll' : (L₁' ++ L₂' ++ L₃').length = n := by rwa [←h₃']
  have hahi : (L₁ ++ L₂).length = hi := by simpa only [List.length_append, h₁]
  have hahi' : (L₁' ++ L₂').length = hi := by simpa only [List.length_append, h₁']

  have hh1 : L₁ = L₁' := by
    apply List.ext_getElem
    · simp only [h₁, h₁']
    · intro i hil hil'
      have : as.toArray.toList[i] = as'.toArray.toList[i] := hperm.2.1 ⟨i, by omega⟩ (h₁' ▸ hil')
      simp only [h₃, h₃', List.append_assoc] at this
      exact List.getElem_append_left'' hil' ▸ List.getElem_append_left'' hil ▸ this

  have hh3 : L₃ = L₃' := by
    apply List.ext_getElem
    · suffices L₁.length + L₂.length + L₃.length = L₁'.length + L₂'.length + L₃'.length by omega
      suffices (L₁ ++ L₂ ++ L₃).length = (L₁' ++ L₂' ++ L₃').length by simpa only [←List.length_append]
      rw [hlll, hlll']

    · intro j hjl hjl'

      have h : (L₁ ++ L₂).length + j < (L₁ ++ L₂ ++ L₃).length := by
        simp only [List.length_append, Nat.add_assoc, Nat.add_lt_add_iff_left]; exact hjl
      have h' : (L₁' ++ L₂').length + j < (L₁' ++ L₂' ++ L₃').length := by
        simp only [List.length_append, Nat.add_assoc, Nat.add_lt_add_iff_left]; exact hjl'
      suffices (L₁ ++ L₂ ++ L₃)[(L₁ ++ L₂).length + j]'(h) = (L₁' ++ L₂' ++ L₃')[(L₁' ++ L₂').length + j]'(h') by
        rw [List.getElem_append_right'' hjl] at this
        rw [List.getElem_append_right'' hjl'] at this
        exact this

      simp only [hahi, hahi']
      simp only [←h₃, ←h₃']
      exact hperm.2.2 ⟨hi + j, by omega⟩ (by change _ < hi + j; omega)

  have hh2 : L₂ ~ L₂' :=
    hh1 ▸ hh3 ▸ h₃ ▸ h₃' ▸ (show as.toArray.toList ~ as'.toArray.toList from hperm.1)
    |> (List.perm_append_right_iff _).1
    |> (List.perm_append_left_iff _).1

  let i' := i - left
  have hilen : i' < L₂.length := by omega

  have hieq : i = left + i' := by omega

  have ⟨⟨j', hjlen⟩, hhh0⟩ := List.perm_mem_getElem hh2 ⟨i', by omega⟩ --: ∃ (j' : Fin L₂'.length), L₂'[j'] = L₂[i']

  let j : Fin n := ⟨left + j', by omega⟩

  have hlj : left ≤ j := by change left ≤ left + j'; omega
  have hj : j < hi := by change left + j' < hi; omega

  have : as'[j] = as[i] := by
    simp only [Fin.getElem_fin, hieq]

    change as'.toArray.toList[left + j' ]'(by omega) = as.toArray.toList[left + i' ]'(by omega) -- by simp only [hieq]
    suffices (L₁' ++ L₂' ++ L₃')[L₁'.length + j' ]'(by omega) = (L₁ ++ L₂ ++ L₃)[L₁.length + i' ]'(by omega) by
      simp only [h₁, h₁', ←h₃, ←h₃'] at this; exact this

    simp only [List.append_assoc]

    simp only [List.getElem_append_right'' (l₁ := L₁) (l₂ := L₂ ++ L₃) (n := i') (by simp; omega)]
    simp only [List.getElem_append_right'' (l₁ := L₁') (l₂ := L₂' ++ L₃') (n := j') (by simp; omega)]
    simp only [List.getElem_append_left'' (l₁ := L₂) (l₂ := L₃) hilen]
    simp only [List.getElem_append_left'' (l₁ := L₂') (l₂ := L₃') hjlen]

    exact hhh0

  ⟨j, hlj, hj, this⟩

/-- The "converse" of the PermStabilizing'.defn is a trivial corollary -/
example {n left hi : Nat} {as as' : Vector α n}
    (hperm : PermStabilizing' left (hi - 1) as as') (hr' : hi ≤ n) :
    ∀ (i : Fin n) (_ : left ≤ i) (_ : i < hi),
    ∃ (j : Fin n) (_ : left ≤ j) (_ : j < hi),
    as[j] = as'[i] :=
  PermStabilizing'.mem_getElem hperm.symm hr'

protected theorem PermStabilizing'.invariance {motive : α → Sort 0} {n left hi : Nat} {arr arr' : Vector α n}
    (hperm : PermStabilizing' left (hi - 1) arr' arr) (hr' : hi ≤ n) (h : ∀ (k : Fin n) (_ : left ≤ k) (_ : k < hi), (motive arr[k])):
 (∀ (k : Fin n) (_ : left ≤ k) (_ : k < hi), (motive arr'[k]))
:= fun  k h1 h2 =>
    have ⟨j, w1', w2', this⟩ := PermStabilizing'.mem_getElem hperm hr' k h1 h2
    (congrArg motive this) ▸ (h j  w1' w2')
