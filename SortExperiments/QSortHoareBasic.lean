

module
import Quicksort.Init.Ord

-- @[simp, grind .]
-- theorem dbgTraceIfShared_noop : (dbgTraceIfShared s a) = a := rfl

@[specialize]
structure Pivot (α: Type u) (n : Nat)  where
  piv' : α
  arr' : Vector α n
  deriving Repr, Nonempty, Inhabited

@[inline]
def Pivot.maybeSwap [Ord α] (as : Vector α n) (low high : Fin n) : Vector α n :=
  if compare as[high] as[low] |>.isLT then
    -- (dbgTraceIfShared "Pivot.maybeSwap `as` is shared!" as).swap low high
    as.swap low high
  else
    as

@[inline]
def Pivot.median_of_three [Ord α] (arr : Vector α n) (left : Nat)  (right : Nat) (hlr : left < right) (hr : right < n) : Pivot α n:=
  have hl : left < n := by omega

  let mid := left + ((right - left + 1)/2)
  have hm : mid < n := by omega
  let arr_ := arr
    |> (maybeSwap · ⟨left, hl⟩ ⟨mid, hm⟩)
    |> (maybeSwap · ⟨left, hl⟩ ⟨right, hr⟩)
    |> (maybeSwap · ⟨mid, hm⟩ ⟨right, hr⟩)

  let pivot := arr_[mid]
  ⟨pivot, arr_⟩






theorem Pivot.maybeSwap_sorted [Ord α]  (lt_asymm : ∀ {x y : α}, (compare x y |>.isLT) → ¬(compare y x |>.isLT))  (as : Vector α n) (low high : Nat) (hlh : low ≤ high) (hn : high < n) : ¬ (compare (maybeSwap as ⟨low, by omega⟩ ⟨high, by omega⟩)[high] (maybeSwap as ⟨low, by omega⟩ ⟨high, by omega⟩)[low] |>.isLT) := by
  unfold maybeSwap; split
  · next h =>
      grind [as.getElem_swap_right, as.getElem_swap_left]
  · assumption


open Ord in
theorem Pivot.median_of_three_sorted [Ord α]
    (not_lt : ∀ {x y : α}, ¬(compare y x |>.isLT) ↔ (compare x y |>.isLE) := by grind)
    (le_trans : ∀ {x y z : α}, (compare x y).isLE → (compare y z).isLE → (compare x z).isLE := by grind)
    {arr : Vector α n} {left right: Nat} (hlr : left < right) (hr : right < n) :
    let ⟨pivot, arr_⟩ := median_of_three arr left right hlr hr;
    ¬(compare pivot arr_[left] |>.isLT) ∧ ¬(compare arr_[right] pivot |>.isLT) := by
  have lt_asymm : ∀ {x y : α}, (compare x y |>.isLT) → ¬(compare y x |>.isLT) := by grind
  have le_trans' : ∀ {x y z : α}, ¬(compare y x |>.isLT) → ¬(compare z y |>.isLT) → ¬(compare z x |>.isLT) := by grind

  let mid := left + ((right - left + 1)/2)

  have _ : left < n := by omega
  have _ : mid < n := by omega

  have hlm : left ≤ mid := by omega
  have hmr : mid ≤ right := by omega
  let arr1 : Vector α n := maybeSwap arr ⟨left, by omega⟩ ⟨mid, by omega⟩
  let arr2 : Vector α n := maybeSwap arr1 ⟨left, by omega⟩ ⟨right, by omega⟩
  let arr_ : Vector α n := maybeSwap arr2 ⟨mid, by omega⟩ ⟨right, by omega⟩

  change ¬(compare arr_[mid] arr_[left] |>.isLT) ∧ ¬(compare arr_[right] arr_[mid] |>.isLT)

  have hh1 : ¬(compare arr1[mid] arr1[left] |>.isLT) := maybeSwap_sorted lt_asymm arr left mid (by omega) (by omega)
  have hh2 : ¬(compare arr2[right] arr2[left] |>.isLT) := maybeSwap_sorted lt_asymm arr1 left right (by omega) (by omega)
  have hh_ : ¬(compare arr_[right] arr_[mid] |>.isLT) := maybeSwap_sorted lt_asymm arr2 mid right (by omega) (by omega)

  suffices ¬(compare arr_[mid] arr_[left] |>.isLT) from ⟨this, hh_⟩

  if hleqm : left = mid then
    simp only [hleqm]
    exact lt_irrefl lt_asymm arr_[mid]
  else
    have hlneqr : left ≠ right := by omega
    simp only [arr_]
    unfold maybeSwap
    split
    · have : (arr2.swap mid right)[left] = _ :=
        arr2.getElem_swap_of_ne hleqm hlneqr
      grind [arr2.getElem_swap_left]
    · if hmeqr : mid = right then
        simp only [hmeqr]
        exact hh2
      else
        simp only [arr2]
        unfold maybeSwap
        split

        · have : (arr1.swap left right)[mid] = _ :=
            arr1.getElem_swap_of_ne (Ne.symm hleqm) hmeqr
          grind [arr1.getElem_swap_left]
        · assumption

@[specialize]
structure Partition (α: Type u) (n : Nat)  where
  arr' : Vector α n
  j' : Nat
  i' : Nat
  deriving Repr, Nonempty, Inhabited

@[inline]
def Partition.hoare [Ord α] (arr : Vector α n) (pivot : α) (left : Nat)  (right : Nat) (hlr : left < right)
    (hr : right < n) (halgep : ¬(compare pivot arr[left] |>.isLT)) (harltp : ¬(compare arr[right] pivot |>.isLT)) :
    {x : Partition α n // (left < x.i') ∧ (x.j' < right)} :=
  have hl : left < n := by omega

  let rec @[specialize] loop (pivot : α) (arr : Vector α n) (i j : Nat) (hli : left < i)
      (hij : i ≤ j + 1) (hjr : j < right) (halgep : ¬(compare pivot arr[left] |>.isLT)) (harltp : ¬(compare arr[right] pivot |>.isLT)) :=

    let ⟨i', _, _⟩ := while_i left right hr pivot arr i j (by omega) harltp
      i Nat.le.refl (by omega)

    let ⟨j', _⟩  := while_j left right hr hl pivot arr i' j hjr (by omega) halgep
      j (by omega) Nat.le.refl

    if _ : i' < j' then
      -- let arr' := (dbgTraceIfShared "Partition.hoare `as` is shared!" arr).swap i' j'
      let arr' := arr.swap i' j'
      have halgep' : ¬(compare pivot arr'[left] |>.isLT)  := by
        simp only [show arr'[left] = _ by apply Vector.getElem_swap_of_ne ..; all_goals omega]
        exact halgep
      have harltp' : ¬(compare arr'[right] pivot |>.isLT) := by
        simp only [show arr'[right] = _ by apply Vector.getElem_swap_of_ne ..; all_goals omega]
        exact harltp

      loop pivot arr' (i' + 1) (j' - 1) (by omega) (by omega) (by omega) halgep' harltp'
    else if _ : j' < i' then
      ⟨⟨arr, j', i'⟩, by simp; omega, by simp; omega⟩
    else -- have _ : j' = i' := by omega
      ⟨⟨arr, j' - 1, i' + 1⟩, by simp; omega, by simp; omega⟩
  loop pivot arr (left + 1) (right - 1) Nat.le.refl (by omega) (by omega) halgep harltp
where
  @[inline, specialize]
  while_i [Ord α] (left right : Nat) (hr : right < n) (pivot : α) (arr : Vector α n)
      (i j : Nat) (hjr : j < right) (harltp : ¬(compare arr[right] pivot |>.isLT))
      (ival : Nat) (hii : i ≤ ival) (hxi : ival ≤ right) : { i' : Fin n // i ≤ i' ∧ i' ≤ right } :=
    have hi : ival < n := by omega
    if h' : compare arr[ival] pivot |>.isLT then
      have _ : ival ≠ right := by grind
      while_i left right hr pivot arr i j hjr harltp   (ival + 1) (by omega) (by omega)
    else
      ⟨⟨ival, by omega⟩, hii, hxi⟩

  @[inline, specialize]
  while_j [Ord α] (left right : Nat) (hr : right < n) (hl : left < n) (pivot : α)
      (arr : Vector α n) (i j : Nat)  (hjr : j < right) (hli : left < i) (halgep : ¬(compare pivot arr[left] |>.isLT))
      (jval : Nat) (hxj : left ≤ jval) (hjj : jval ≤ j) : { j' : Fin n // j' ≤ j } :=
    have hj : jval < n := by omega
    if h' : compare pivot arr[jval] |>.isLT then
      have _ : jval ≠ left := by grind
      while_j left right hr hl pivot arr i j hjr hli halgep   (jval - 1) (by omega) (by omega)
    else
      ⟨⟨jval, by omega⟩, hjj⟩



-- /-- info: { arr' := { toArray := #[4, 3, 1, 0, 5, 2, 6, 8, 7, 9], size_toArray := _ }, j' := 5, i' := 6 } -/
-- #guard_msgs(info) in #eval! Partition.hoare sorry sorry #v[9,  3,  1,  8,  6,  2,  5,  0,  7,  4]  0 9 (by omega) (by omega)

-- /-- info: { arr' := { toArray := #[4, 3, 1, 0, 6, 2, 6, 8, 7, 9], size_toArray := _ }, j' := 5, i' := 6 } -/
-- #guard_msgs(info) in #eval! Partition.hoare sorry sorry #v[9,  3,  1,  8,  6,  2,  6,  0,  7,  4]  0 9 (by omega) (by omega)

-- /-- info: { arr' := { toArray := #[4, 3, 1, 0, 6, 2, 6, 8, 7, 9], size_toArray := _ }, j' := 5, i' := 6 } -/
-- #guard_msgs(info) in #eval! Partition.hoare sorry sorry #v[9,  3,  1,  8,  6,  2,  6,  0,  7,  4]  0 9 (by omega) (by omega)

-- /-- info: { arr' := { toArray := #[0, 0, 0, 1, 2], size_toArray := _ }, j' := 1, i' := 2 } -/
-- #guard_msgs(info) in #eval! Partition.hoare sorry sorry #v[2, 0, 0, 1, 0]  0 4 (by omega) (by omega)


section
variable
  [Ord α]
  -- [ile_trans : Std.TransOrd α]


open Ord in

@[inline]
public def qsort (arr : Array α) /- (left : Nat := 0) -/ /- (right := arr.size - 1) -/
    (not_lt : ∀ {x y : α}, ¬(compare y x |>.isLT) ↔ (compare x y |>.isLE) := by grind)
    (le_trans : ∀ {x y z : α}, (compare x y).isLE → (compare y z).isLE → (compare x z).isLE := by grind)
    : Array α :=
  let rec @[specialize]
  recurse {n} (as : Vector α n) (left : Nat) (right: Nat) (hsize' : right ≤ n - 1) : Vector α n :=
    if hlr : left < right then
      have hr : right < n := by omega

      let v := Pivot.median_of_three as left right hlr hr
      have : ¬(compare v.piv' v.arr'[left] |>.isLT) ∧ ¬(compare v.arr'[right] v.piv' |>.isLT) :=
        Pivot.median_of_three_sorted not_lt le_trans hlr hr

      let ⟨⟨a, j', i'⟩, (_ : _ < i'), (_ : j' < _ )⟩ :=
        Partition.hoare v.arr' v.piv' left right hlr hr  this.left this.right

      recurse a left j' (by omega)
      |>
      (recurse · i' right (by omega))
    else
      as
    -- termination_by right - left

  -- let right' : Nat := if right ≤ arr.size - 1 then right else
  --   have := Inhabited.mk (arr.size - 1)
  --   panic! "index out of bounds"

  -- have : right' ≤ arr.size - 1 := by
  --   grind [panicWithPosWithDecl, panic, panicCore]

  -- strict ⟨arr, rfl⟩ 0 right' this |>.1
  recurse ⟨arr, rfl⟩ 0 (arr.size - 1) (by omega) |>.1
end


/--
info: #[0, 0, 0, 1, 3, 3, 3, 4, 4, 4, 5, 6, 7, 8, 10, 11, 13, 14, 14, 14, 16, 17, 18, 19, 24, 24, 24, 25, 26, 27, 29, 29, 30,
  30, 32, 33, 34, 34, 35, 37, 37, 39, 39, 39, 39, 40, 40, 41, 42, 42, 43, 43, 46, 47, 49, 50, 50, 52, 53, 53, 53, 54,
  56, 56, 57, 58, 60, 60, 61, 63, 65, 68, 69, 70, 73, 75, 76, 77, 78, 79, 81, 84, 84, 85, 86, 88, 89, 90, 90, 91, 91,
  91, 91, 93, 94, 95, 95, 96, 99, 99]
-/
#guard_msgs in
#eval! qsort #[
  56, 69, 30, 11, 34, 14, 95, 81, 96, 76,
  91, 24, 13, 39, 42, 14, 46, 3, 4, 61,
  84, 68, 58, 39, 95, 85, 34, 29, 47, 3,
  40, 8, 91, 60, 43, 88, 25, 39, 35, 89,
  5, 37, 90, 94, 86, 53, 43, 39, 14, 29,
  10, 91, 77, 24, 32, 99, 7, 3, 37, 73,
  63, 0, 30, 57, 93, 79, 27, 1, 17, 53,
  4, 0, 6, 65, 16, 18, 70, 54, 90, 41,
  42, 78, 52, 50, 49, -0, 19, 40, 33, 26,
  84, 75, 99, 4, 91, 50, 53, 60, 56, 24
]


-- def main (args : List String) : IO UInt32 := do
--   let out := qsort args.toArray
--   IO.println s!"{out}"
--   return 0

-- #eval main ["momo", "somo", "aaa"]
