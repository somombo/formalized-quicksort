import Batteries.Data.Array.Lemmas
import Battteries.List.Lemmas

namespace Array

theorem swap_self (a : Array α) (i : Fin a.size) : a.swap i i = a := by
  apply ext
  · simp only [size_swap]
  · intros
    simp only [getElem_swap]
    split <;> simp_all

theorem swap_of_append (as : Array α)
  {A a B b C} {i j} (hi : A.length = i.1) (hj : i.1 + B.length + 1 = j.1)
    (eq1 : as.toList = A ++ a :: B ++ b :: C) :
    (as.swap i j).toList = A ++ b :: B ++ a :: C := by
  simp only [swap, get, toList_set, Fin.cast_mk,
    fun a b => show ∀ (e : b = a) (v : Fin b), (e ▸ v) = v.cast e by rintro rfl v; rfl]
  rw [show as.toList.get _ = _ from List.get_of_append' (by simpa using eq1) hi]
  rw [List.set_of_append (l₁ := A ++ b :: B) (a := b) (l₂ := C) _ ?_ (by simp [hi, ← hj]; rfl)]
  rw [show as.toList.get _ = _ from List.get_of_append' eq1 (by simp [hi, ← hj]; rfl)]
  rw [List.set_of_append (l₁ := A) (a := a) (l₂ := B ++ b :: C) _ (by simp [eq1]) hi]
  simp
