import Quicksort.Init.Ord

@[inline]
def Vector.maybeSwap [Ord α] (as : Vector α n) (low high : Fin n) : Vector α n :=
  if lt as[high] as[low] then
    as.swap low high
  else
    as

structure Partition (α: Type u) (n : Nat)  where
  arr' : Vector α n
  j' : Nat
  i' : Nat
  deriving Repr, Nonempty, Inhabited

-- set_option linter.unusedVariables false in
-- abbrev Partition.Scheme (α: Type u) [Ord α] := {n : Nat} → Vector α n → (left right : Nat) → left < right → right < n →  { x : Partition α n  // left < x.i' ∧ x.j' < right }

open Vector

namespace Partition

variable [Ord α]
variable (lt_asymm : ∀ {x y : α}, lt x y → ¬lt y x)

include lt_asymm in
private theorem lt_irrefl : ∀ (x : α), ¬lt x x :=
  fun _ h => (lt_asymm h) h

include lt_asymm in
theorem maybeSwap_sorted (as : Vector α n) (low high : Nat) (hlh : low ≤ high) (hn : high < n) : ¬ (lt (maybeSwap as ⟨low, by omega⟩ ⟨high, by omega⟩)[high] (maybeSwap as ⟨low, by omega⟩ ⟨high, by omega⟩)[low]) := by
  unfold maybeSwap; split
  · next h =>
      simp only [as.getElem_swap_right, as.getElem_swap_left]
      exact lt_asymm h
  · assumption

open Ord in
theorem median_of_three_sorted [Std.TransOrd α] {arr : Vector α n} {left mid right: Nat} (hlm : left ≤ mid) (hmr : mid ≤ right) (hr : right < n) :
  let arr_ := arr
    |> (maybeSwap · ⟨left, by omega⟩ ⟨mid, by omega⟩)
    |> (maybeSwap · ⟨left, by omega⟩ ⟨right, by omega⟩)
    |> (maybeSwap · ⟨mid, by omega⟩ ⟨right, by omega⟩)

  ¬lt arr_[mid] arr_[left] ∧ ¬lt arr_[right] arr_[mid]
  :=
  have _ : left < n := by omega
  have _ : mid < n := by omega

  let arr1 : Vector α n := maybeSwap arr ⟨left, by omega⟩ ⟨mid, by omega⟩
  let arr2 : Vector α n := maybeSwap arr1 ⟨left, by omega⟩ ⟨right, by omega⟩
  let arr_ : Vector α n := maybeSwap arr2 ⟨mid, by omega⟩ ⟨right, by omega⟩

  have hh1 : ¬lt arr1[mid] arr1[left] := maybeSwap_sorted lt_asymm arr left mid (by omega) (by omega)
  have hh2 : ¬lt arr2[right] arr2[left] := maybeSwap_sorted lt_asymm arr1 left right (by omega) (by omega)
  have hh_ : ¬lt arr_[right] arr_[mid] := maybeSwap_sorted lt_asymm arr2 mid right (by omega) (by omega)

  suffices ¬lt arr_[mid] arr_[left] from ⟨this, hh_⟩

  if hleqm : left = mid then by
    simp only [hleqm]
    exact lt_irrefl lt_asymm arr_[mid]
  else by
    have hlneqr : left ≠ right := by omega
    simp only [arr_]
    unfold maybeSwap
    split
    · have : (arr2.swap mid right)[left] = _ :=
        arr2.getElem_swap_of_ne hleqm hlneqr
      simp only [this, arr2.getElem_swap_left]
      assumption
    · exact
      if hmeqr : mid = right then by
        simp only [hmeqr]
        exact hh2
      else by
        simp only [arr2]
        unfold maybeSwap
        split

        · have : (arr1.swap left right)[mid] = _ :=
            arr1.getElem_swap_of_ne (Ne.symm hleqm) hmeqr
          simp only [this, arr1.getElem_swap_left]
          refine le_trans' (lt_asymm ?_) hh1
          assumption
        · assumption
end Partition



namespace Partition.hoare
open Vector
variable [Ord α]


@[inline]
def eager [Ord α] {n : Nat} (arr : Vector α n) (left : Nat)  (right : Nat) (hlr : left < right) (hr : right < n) : {x : Partition α n // (left < x.i') ∧ (x.j' < right)} :=
  let mid := left + ((right - left)/2)
  let arr_ := arr
    |> (maybeSwap · ⟨left, by omega⟩ ⟨mid, by omega⟩)
    |> (maybeSwap · ⟨left, by omega⟩ ⟨right, by omega⟩)
    |> (maybeSwap · ⟨mid, by omega⟩ ⟨right, by omega⟩)
  have pivot := arr_[mid]

  let rec @[specialize] loop (arr : Vector α n) (i j : Nat) (hli : left < i) (hij : i ≤ j + 1) (hjr : j < right) : { x : Partition α n // left < x.i' ∧ x.j' < right } :=
    if _ : j < i then
      ⟨⟨arr, j, i⟩, ⟨hli, hjr⟩⟩
    else
      if (lt arr[i] pivot)  then
        loop arr (i + 1) j (by omega) (by omega) (by omega)
      else if (lt pivot arr[j]) then
        loop arr i (j - 1) (by omega) (by omega) (by omega)
      else
        if hlt : i < j then
          loop (arr.swap i j ) (i + 1) (j - 1) (by omega) (by omega) (by omega)
        else
          ⟨⟨arr, j - 1, i + 1⟩, ⟨(by omega : _ < i + 1), (by omega : j - 1 < _)⟩⟩
  -- termination_by j + 1 - i

  loop arr_ (left + 1) (right - 1) (by omega) (by omega) (by omega)

/-- info: { arr' := { toArray := #[4, 3, 1, 0, 5, 2, 6, 8, 7, 9], size_toArray := _ }, j' := 5, i' := 6 } -/
#guard_msgs(info) in #eval Partition.hoare.eager #v[9,  3,  1,  8,  6,  2,  5,  0,  7,  4]  0 9 (by omega) (by omega)

/-- info: { arr' := { toArray := #[4, 3, 1, 0, 6, 2, 6, 8, 7, 9], size_toArray := _ }, j' := 5, i' := 6 } -/
#guard_msgs(info) in #eval Partition.hoare.eager #v[9,  3,  1,  8,  6,  2,  6,  0,  7,  4]  0 9 (by omega) (by omega)

/-- info: { arr' := { toArray := #[4, 3, 1, 0, 6, 2, 6, 8, 7, 9], size_toArray := _ }, j' := 5, i' := 6 } -/
#guard_msgs(info) in #eval Partition.hoare.eager #v[9,  3,  1,  8,  6,  2,  6,  0,  7,  4]  0 9 (by omega) (by omega)

/-- info: { arr' := { toArray := #[0, 0, 0, 1, 2], size_toArray := _ }, j' := 1, i' := 2 } -/
#guard_msgs(info) in #eval Partition.hoare.eager #v[2, 0, 0, 1, 0]  0 4 (by omega) (by omega)


namespace classic

@[inline, specialize]
def loop.while_i (left right : Nat) (hr : right < n) (pivot : α) (arr : Vector α n)
    (i j : Nat) (hjr : j < right) (harltp : ¬lt arr[right] pivot)
    (ival : Nat) (hii : i ≤ ival) (hxi : ival ≤ right) : { i' : Fin n // i ≤ i' ∧ i' ≤ right } :=
  have hi : ival < n := by omega
  if h' : lt arr[ival] pivot /- ∧ ival ≤ j -/ then
    have _ : ival ≠ right := /- by omega -/
      (h' |> show ¬lt arr[ival] pivot by simpa only [·])
    while_i left right hr pivot arr i j hjr harltp   (ival + 1) (by omega) (by omega)
  else
    ⟨⟨ival, by omega⟩, hii, hxi⟩

@[inline, specialize]
def loop.while_j (left right : Nat) (hr : right < n) (hl : left < n) (pivot : α)
    (arr : Vector α n) (i j : Nat)  (hjr : j < right) (hli : left < i) (halgep : ¬lt pivot arr[left])
    (jval : Nat) (hxj : left ≤ jval) (hjj : jval ≤ j) : { j' : Fin n // j' ≤ j } :=
  have hj : jval < n := by omega
  if h' : lt pivot arr[jval] /- ∧ i ≤ jval -/ then
    have _ : jval ≠ left := /- by omega -/
      (h' |> show ¬lt pivot arr[jval] by simpa only [·])
    while_j left right hr hl pivot arr i j hjr hli halgep   (jval - 1) (by omega) (by omega)
  else
    ⟨⟨jval, by omega⟩, hjj⟩


open Ord in
@[inline]
def _root_.Partition.hoare.classic  [inst_le_trans : Std.TransOrd α] (arr : Vector α n) (left : Nat)  (right : Nat) (hlr : left < right)
    (hr : right < n) : {x : Partition α n // (left < x.i') ∧ (x.j' < right)} :=
  -- have lt_asymm : ∀ {x y : α}, lt x y → ¬lt y x := by grind
  -- have le_trans' : ∀ {x y z : α}, ¬lt y x → ¬lt z y → ¬lt z x := by grind
  have hl : left < n := by omega

  let rec @[specialize] loop (pivot : α) (arr : Vector α n) (i j : Nat) (hli : left < i)
      (hij : i ≤ j + 1) (hjr : j < right) (halgep : ¬lt pivot arr[left]) (harltp : ¬lt arr[right] pivot) :=

    let ⟨i', _, _⟩ := loop.while_i left right hr pivot arr i j (by omega) harltp
      i Nat.le.refl (by omega)

    let ⟨j', _⟩  := loop.while_j left right hr hl pivot arr i' j hjr (by omega) halgep
      j (by omega) Nat.le.refl

    if _ : i' < j' then
      let arr' := arr.swap i' j'
      have halgep' : ¬lt pivot arr'[left]  := by
        simp only [show arr'[left] = _ by apply Vector.getElem_swap_of_ne ..; all_goals omega]
        exact halgep
      have harltp' : ¬lt arr'[right] pivot := by
        simp only [show arr'[right] = _ by apply Vector.getElem_swap_of_ne ..; all_goals omega]
        exact harltp

      loop pivot arr' (i' + 1) (j' - 1) (by omega) (by omega) (by omega) halgep' harltp'
    else if _ : j' < i' then
      ⟨⟨arr, j', i'⟩, by simp; omega, by simp; omega⟩
    else -- have _ : j' = i' := by omega
      ⟨⟨arr, j' - 1, i' + 1⟩, by simp; omega, by simp; omega⟩
  -- termination_by j + 1 - i
  -- decreasing_by omega

  let mid := left + ((right - left)/2)
  have hm : mid < n := by omega
  let arr_ := arr
    |> (maybeSwap · ⟨left, hl⟩ ⟨mid, hm⟩)
    |> (maybeSwap · ⟨left, hl⟩ ⟨right, hr⟩)
    |> (maybeSwap · ⟨mid, hm⟩ ⟨right, hr⟩)
  let pivot := arr_[mid]

  have : ¬lt pivot arr_[left] ∧ ¬lt arr_[right] pivot :=
    median_of_three_sorted  (by omega) (by omega) hr
  loop pivot arr_ (left + 1) (right - 1) Nat.le.refl (by omega) (by omega) this.left this.right

/-- info: { arr' := { toArray := #[4, 3, 1, 0, 5, 2, 6, 8, 7, 9], size_toArray := _ }, j' := 5, i' := 6 } -/
#guard_msgs(info) in #eval Partition.hoare.classic #v[9,  3,  1,  8,  6,  2,  5,  0,  7,  4]  0 9 (by omega) (by omega)

/-- info: { arr' := { toArray := #[4, 3, 1, 0, 6, 2, 6, 8, 7, 9], size_toArray := _ }, j' := 5, i' := 6 } -/
#guard_msgs(info) in #eval Partition.hoare.classic #v[9,  3,  1,  8,  6,  2,  6,  0,  7,  4]  0 9 (by omega) (by omega)

/-- info: { arr' := { toArray := #[4, 3, 1, 0, 6, 2, 6, 8, 7, 9], size_toArray := _ }, j' := 5, i' := 6 } -/
#guard_msgs(info) in #eval Partition.hoare.classic #v[9,  3,  1,  8,  6,  2,  6,  0,  7,  4]  0 9 (by omega) (by omega)

/-- info: { arr' := { toArray := #[0, 0, 0, 1, 2], size_toArray := _ }, j' := 1, i' := 2 } -/
#guard_msgs(info) in #eval Partition.hoare.classic #v[2, 0, 0, 1, 0]  0 4 (by omega) (by omega)

end  classic
end Partition.hoare


@[specialize]
def Partition.hoare [ord : Ord α] (arr : Vector α n) (left : Nat)  (right : Nat) (hlr : left < right) (hr : right < n) : {x : Partition α n // (left < x.i') ∧ (x.j' < right)} :=
  have hl : left < n := by omega

  let mid := left + ((right - left)/2)
  have hm : mid < n := by omega
  let arr_ := arr
    |> (maybeSwap · ⟨left, hl⟩ ⟨mid, hm⟩)
    |> (maybeSwap · ⟨left, hl⟩ ⟨right, hr⟩)
    |> (maybeSwap · ⟨mid, hm⟩ ⟨right, hr⟩)

  let pivot := arr_[mid]

  if hmo3sortd : ¬lt pivot arr_[left] ∧ ¬lt arr_[right] pivot then
    hoare.classic.loop left right hr hl pivot arr_ (left + 1) (right - 1) Nat.le.refl (by omega) (by omega) hmo3sortd.left hmo3sortd.right
  else
    have := hoare.eager.loop left right hr pivot arr_ (left + 1) (right - 1) (by omega) (by omega) (by omega)
    |> (Inhabited.mk ·)
    panic! "non-asymmetric or non-transitive comparitor. falling back to eager version of partition scheme"


@[inline]
def qsort_hoare_strict [ord : Ord α] [ile_trans : Std.TransOrd α] (arr : Array α) (left : Nat := 0) (right : Nat := arr.size - 1) : Array α :=
  let rec @[specialize]
  sort {n : Nat} (as : Vector α n) (left : Nat := 0) (right : Nat := n - 1) (hsize' : right ≤ n - 1) : Vector α n :=
    if hlr : left < right then
      let ⟨⟨as', j', i'⟩, (_ : _ < i'), (_ : j' < _ )⟩ := Partition.hoare.classic as left right hlr (by omega)
      let as := sort as' left j' (by omega)
      let as := sort as i' right (by omega)
      as
    else
      as
    termination_by right - left

  let right' : Nat := if right ≤ arr.size - 1 then right else
    have := Inhabited.mk (arr.size - 1)
    panic! "index out of bounds"

  have : right' ≤ arr.size - 1 := by
    simp [right']; split <;> simp [panicWithPosWithDecl, panic, panicCore, *]

  sort ⟨arr, rfl⟩ left right' this |>.1


@[inline]
def qsort_hoare  [ord : Ord α] (arr : Array α) (left : Nat := 0) (right : Nat := arr.size - 1) : Array α :=
  let rec @[specialize]
  sort {n : Nat} (as : Vector α n) (left : Nat := 0) (right : Nat := n - 1) (hsize' : right ≤ n - 1) : Vector α n :=
    if hlr : left < right then
      let ⟨⟨as', j', i'⟩, (_ : _ < i'), (_ : j' < _ )⟩ := Partition.hoare as left right hlr (by omega)
      let as := sort as' left j' (by omega)
      let as := sort as i' right (by omega)
      as
    else
      as
    termination_by right - left

  let right' : Nat := if right ≤ arr.size - 1 then right else
    have := Inhabited.mk (arr.size - 1)
    panic! "index out of bounds"

  have : right' ≤ arr.size - 1 := by
    simp [right']; split <;> simp [panicWithPosWithDecl, panic, panicCore, *]

  sort ⟨arr, rfl⟩ left right' this |>.1
