module
public import Quicksort.Init.Ord

public import SortExperiments.Partitioning.Init

@[inline, specialize]
private def while_i [Ord α] (left right : Nat) (hr : right < n) (pivot : α) (arr : Vector α n)
      (i j : Nat) (hjr : j < right) (harltp : ¬lt arr[right] pivot)
      (ival : Nat) (hii : i ≤ ival) (hxi : ival ≤ right) : { i' : Fin n // i ≤ i' ∧ i' ≤ right } :=
    have hi : ival < n := by omega
    if h' : lt arr[ival] pivot then
      have _ : ival ≠ right := by grind
      while_i left right hr pivot arr i j hjr harltp   (ival + 1) (by omega) (by omega)
    else
      ⟨⟨ival, by omega⟩, hii, hxi⟩

@[inline, specialize]
private def while_j [Ord α] (left right : Nat) (hr : right < n) (hl : left < n) (pivot : α)
      (arr : Vector α n) (i j : Nat)  (hjr : j < right) (hli : left < i) (halgep : ¬lt pivot arr[left])
      (jval : Nat) (hxj : left ≤ jval) (hjj : jval ≤ j) : { j' : Fin n // j' ≤ j } :=
    have hj : jval < n := by omega
    if h' : lt pivot arr[jval] then
      have _ : jval ≠ left := by grind
      while_j left right hr hl pivot arr i j hjr hli halgep   (jval - 1) (by omega) (by omega)
    else
      ⟨⟨jval, by omega⟩, hjj⟩


@[inline]
public def Partitioning.hoare [Ord α] {n : Nat} (arr : Vector α n) (pivot : α) (left : Nat)  (right : Nat) (hlr : left < right)
    (hr : right < n) (halgep : ¬(lt pivot arr[left])) (harltp : ¬(lt arr[right] pivot)) :
    {x : Partitioning α n // (left < x.i') ∧ (x.j' < right)} :=
  have hl : left < n := by omega

  let rec @[specialize] loop (pivot : α) (arr : Vector α n) (i j : Nat) (hli : left < i)
      (hij : i ≤ j + 1) (hjr : j < right) (halgep : ¬(lt pivot arr[left])) (harltp : ¬(lt arr[right] pivot)) :=

    let ⟨i', _, _⟩ := while_i left right hr pivot arr i j (by omega) harltp
      i Nat.le.refl (by omega)

    let ⟨j', _⟩  := while_j left right hr hl pivot arr i' j hjr (by omega) halgep
      j (by omega) Nat.le.refl

    if _ : i' < j' then
      -- let arr' := (dbgTraceIfShared "Partitioning.hoare `as` is shared!" arr).swap i' j'
      let arr' := arr.swap i' j'
      have halgep' : ¬(lt pivot arr'[left])  := by
        simp only [show arr'[left] = _ by apply Vector.getElem_swap_of_ne ..; all_goals omega]
        exact halgep
      have harltp' : ¬(lt arr'[right] pivot) := by
        simp only [show arr'[right] = _ by apply Vector.getElem_swap_of_ne ..; all_goals omega]
        exact harltp

      loop pivot arr' (i' + 1) (j' - 1) (by omega) (by omega) (by omega) halgep' harltp'
    else if _ : j' < i' then
      ⟨⟨arr, j', i'⟩, by grind, by grind⟩
    else -- have _ : j' = i' := by omega
      ⟨⟨arr, j' - 1, i' + 1⟩, by simp; omega, by simp; omega⟩
  loop pivot arr (left + 1) (right - 1) Nat.le.refl (by omega) (by omega) halgep harltp



public abbrev Partitioning.Scheme α [Ord α] :=   {n : Nat} → (arr : Vector α n) → (pivot : α) → (left : Nat) → (right : Nat) → (hlr : left < right) → (hr : right < n) →  { x : Partitioning α n  // left < x.i' ∧ x.j' < right }

-- example [Ord α] : Partitioning.Scheme α :=  (@Partitioning.hoare _ _ _ · · · · · · (halgep :=  sorry) (harltp := sorry))


-- /-- info: { arr' := { toArray := #[4, 3, 1, 0, 5, 2, 6, 8, 7, 9], size_toArray := _ }, j' := 5, i' := 6 } -/
-- #guard_msgs(info) in #eval! Partitioning.hoare sorry sorry #v[9,  3,  1,  8,  6,  2,  5,  0,  7,  4]  0 9 (by omega) (by omega)

-- /-- info: { arr' := { toArray := #[4, 3, 1, 0, 6, 2, 6, 8, 7, 9], size_toArray := _ }, j' := 5, i' := 6 } -/
-- #guard_msgs(info) in #eval! Partitioning.hoare sorry sorry #v[9,  3,  1,  8,  6,  2,  6,  0,  7,  4]  0 9 (by omega) (by omega)

-- /-- info: { arr' := { toArray := #[4, 3, 1, 0, 6, 2, 6, 8, 7, 9], size_toArray := _ }, j' := 5, i' := 6 } -/
-- #guard_msgs(info) in #eval! Partitioning.hoare sorry sorry #v[9,  3,  1,  8,  6,  2,  6,  0,  7,  4]  0 9 (by omega) (by omega)

-- /-- info: { arr' := { toArray := #[0, 0, 0, 1, 2], size_toArray := _ }, j' := 1, i' := 2 } -/
-- #guard_msgs(info) in #eval! Partitioning.hoare sorry sorry #v[2, 0, 0, 1, 0]  0 4 (by omega) (by omega)
