import Quicksort.Partition.Hoare.Classic.Basic
import Quicksort.Partition.Hoare.Eager.Basic

open Vector

def Partition.hoare (arr : Vector α n) (left : Nat)  (right : Nat) (hlr : left < right) (hr : right < n) (lt : α → α → Bool := by exact (· < ·)): {x : Partition α n // (left < x.i') ∧ (x.j' < right)} :=
  have hl : left < n := by omega

  let mid := left + ((right - left)/2)
  have hm : mid < n := by omega
  let arr_ := arr
    |> (maybeSwap (lt := lt) · ⟨left, hl⟩ ⟨mid, hm⟩)
    |> (maybeSwap (lt := lt) · ⟨left, hl⟩ ⟨right, hr⟩)
    |> (maybeSwap (lt := lt) · ⟨mid, hm⟩ ⟨right, hr⟩)

  let pivot := arr_[mid]

  if hmo3sortd : ¬lt pivot arr_[left] ∧ ¬lt arr_[right] pivot then
    hoare.classic.loop (lt := lt) left right hr hl pivot arr_ (left + 1) (right - 1) Nat.le.refl (by omega) (by omega) hmo3sortd.left hmo3sortd.right
  else
    have := hoare.eager.loop (lt := lt) left right hr pivot arr_ (left + 1) (right - 1) (by omega) (by omega) (by omega)
    |> (Inhabited.mk ·)
    panic! "non-asymmetric or non-transitive comparitor. falling back to eager version of hoare partition scheme"
