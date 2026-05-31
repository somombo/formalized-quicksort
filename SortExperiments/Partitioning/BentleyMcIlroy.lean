module
import Quicksort.Init.Ord

public import SortExperiments.Partitioning.Init


@[inline]
private def move_pivots_back (left right : Nat) (hlr : left < right) (hr : right < n)
    (p q : Nat) (hp : p < n) (x : { x : Partitioning α n // left < x.i' ∧ x.j' < right ∧ x.i' ≤ q + 1 }) :
    { x : Partitioning α n // left < x.i' ∧ x.j' < right } :=
  let ⟨⟨arr', j', i'⟩, (_ : left < i'), (_ : j' < right), (_ : i' ≤ q + 1)⟩ := x
  let rec @[specialize] move_p_back (k : Nat) (arr : Vector α n) (j : Nat) (hjr : j < right) :
      Vector α n × Subtype (· < right) :=
    if h : k < p then
      move_p_back (k + 1) (arr.swap k j (by omega) (by omega)) (j - 1) (by omega)
    else
      (arr, ⟨j, by omega⟩)
  let (arr'', ⟨j'', _⟩) := move_p_back (left + 1) arr' j' (by omega)

  let rec @[specialize] move_q_forward (k : Nat) (arr : Vector α n) (i : Nat) (hkq : q + 1 ≤ k) (hli : left < i)
      (hieqk_invar : i = k - (q + 1) + i') : Vector α n × Subtype (left < ·) :=

    if h : k < right then
      move_q_forward (k + 1) (arr.swap k i (by omega) (by omega) ) (i + 1) (by omega) (by omega) (by omega)
    else
      (arr, ⟨i, by omega⟩)


  let (arr''', ⟨i'', _⟩) := move_q_forward (q + 1) arr'' i' (by omega) (by omega) (by omega)

  ⟨⟨arr''', j'', i''⟩, by omega, by omega⟩

variable [Ord α]
open Ord
@[inline]
private def loop.while_j' (left right : Nat) (hr : right < n) (hl : left < n) (pivot : α)
    (arr : Vector α n) (i j : Nat)  (hjr : j < right) (hli : left < i)
    (jval : Nat) (hxj : left ≤ jval) (hjj : jval ≤ j) (halgep : ¬lt pivot arr[left]) :
    { j' : Fin n // j' ≤ j ∧ ¬ lt pivot arr[j'.val] } :=
  have hj : jval < n := by omega
  if h' : lt pivot arr[jval] /- ∧ i ≤ jval -/ then
    have _ : jval ≠ left :=
      (h' |> show ¬lt pivot arr[jval] by simpa only [·])
    while_j' left right hr hl pivot arr i j hjr hli    (jval - 1) (by omega) (by omega) halgep
  else
    ⟨⟨jval, by omega⟩, hjj, h'⟩

@[inline]
private def loop.while_i'  (left right : Nat) (hr : right < n) (pivot : α) (arr : Vector α n)
    (i j : Nat) (hjr : j < right) (ival : Nat) (hii : i ≤ ival) (hxi : ival ≤ right)
    (harltp : ¬lt arr[right] pivot) : { i' : Fin n // i ≤ i' ∧ i' ≤ right ∧  ¬lt arr[i'.val] pivot} :=
  have hi : ival < n := by omega
  if h' : lt arr[ival] pivot then
    have _ : ival ≠ right :=
      (h' |> show ¬lt arr[ival] pivot by simpa only [·])
    while_i' left right hr pivot arr i j hjr    (ival + 1) (by omega) (by omega) harltp
  else
    ⟨⟨ival, by omega⟩, hii, hxi, h'⟩




@[inline]
public def Partitioning.bentleyMcIlroy [Ord α] {n : Nat} (arr : Vector α n) (pivot : α) (left : Nat)  (right : Nat) (hlr : left < right)
    (hr : right < n) (halgep : ¬(compare pivot arr[left] |>.isLT)) (harltp : ¬(compare arr[right] pivot |>.isLT)) :
    {x : Partitioning α n // (left < x.i') ∧ (x.j' < right)} :=
  have hl : left < n := by omega

  have hrr : right - 1 + 1 = right := by omega
  have hll : left + 1 - 1 = left := by omega
  loop pivot arr
    (i := left + 1)
    (j := right - 1)
    (p := left + 1)
    (q := right - 1)
    (by omega) (by omega) (by omega) (by omega)  (by omega) (by omega) (by grind) (by grind)


where
  @[specialize] loop (pivot : α) (arr : Vector α n) (i j : Nat) (p q : Nat)
      (hpi : p ≤ i)  (hqr : q < right) (hli : left < i) (hij : i ≤ j + 1) (hjr : j < right) (hjq : j ≤ q)
      (halgep : ¬lt pivot arr[p - 1]) (haqltp : ¬lt arr[q + 1] pivot)
      : { x : Partitioning α n  // left < x.i' ∧ x.j' < right } :=

    let ⟨⟨j', (_ : j' < n)⟩, (_ : j' ≤ j), hjpiva⟩  := loop.while_j' (p - 1)
      right hr (by omega) pivot arr i j hjr (by omega) j (by omega) Nat.le.refl halgep

    have hjpiva : ¬lt pivot arr[j'] := hjpiva

    let ⟨⟨i', (_ : i' < n)⟩, (_ : i ≤ i'), (_ : i' ≤ q + 1), hapivi⟩ := loop.while_i' left (q + 1)
      (by omega) pivot arr i j' (by omega) i Nat.le.refl (by omega) (by omega)

    have hapivi : ¬lt arr[i'] pivot := hapivi

    if _ : i' < j' then
      have hqsimp : q - 1 + 1 = q := by omega
      have hpsimp : p + 1 - 1 = p := by omega
      let arr' := arr.swap i' j' (by omega) (by omega)

      if _ : lt arr'[i'] pivot then
        if _ : lt pivot arr'[j'] then
          loop pivot arr' (i' + 1) (j' - 1) p q
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by
              -- change ¬lt pivot arr'[p - 1]
              simp only [arr', arr.getElem_swap_of_ne (show p - 1 ≠ i' by omega) (show p - 1 ≠ j' by omega)]
              assumption
            )
            (by
              -- change ¬ lt arr'[q + 1] pivot
              simp only [arr', arr.getElem_swap_of_ne (show q + 1 ≠ i' by omega) (show q + 1 ≠ j' by omega)]
              assumption
            )
        else
          let arr'' := arr'.swap q j' (by omega) (by omega)

          loop pivot arr'' (i' + 1) (j' - 1) p (q - 1)
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by
              -- change ¬lt pivot arr''[p - 1]
              simp only [arr'', Vector.getElem_swap_of_ne (show p - 1 ≠ q by omega) (show p - 1 ≠ j' by omega)]
              simp only [arr', Vector.getElem_swap_of_ne (show p - 1 ≠ i' by omega) (show p - 1 ≠ j' by omega)]
              assumption
            )
            (by
              suffices ¬ lt arr''[q] pivot by simpa only [hqsimp]
              simp only [arr'', Vector.getElem_swap_left]
              simp only [arr', Vector.getElem_swap_right]
              assumption
            )
      else
        let arr'' := arr'.swap p i' (by omega) (by omega)
        if ha'pivj : lt pivot arr''[j'] then

          loop pivot arr'' (i' + 1) (j' - 1) (p + 1) q
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by
              suffices ¬lt pivot arr''[p] by simpa only [hpsimp]
              simp only [arr'', Vector.getElem_swap_left]
              simp only [arr', Vector.getElem_swap_left]
              assumption
            )
            (by
              -- change ¬ lt arr''[q + 1] pivot
              simp only [arr'', Vector.getElem_swap_of_ne (show q + 1 ≠ p by omega) (show q + 1 ≠ i' by omega)]
              simp only [arr', Vector.getElem_swap_of_ne (show q + 1 ≠ i' by omega) (show q + 1 ≠ j' by omega)]
              assumption
            )
        else
          let arr''' := arr''.swap q j' (by omega) (by omega)

          loop pivot arr''' (i' + 1) (j' - 1) (p + 1) (q - 1)
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by
              suffices ¬lt pivot arr'''[p] by simpa only [hpsimp]
              simp only [arr''', Vector.getElem_swap_of_ne (show p ≠ q by omega) (show p ≠ j' by omega)]
              simp only [arr'', Vector.getElem_swap_left]
              simp only [arr', Vector.getElem_swap_left]
              assumption
            )
            (by
              suffices ¬ lt arr'''[q] pivot by simpa only [hqsimp]
              simp only [arr''', Vector.getElem_swap_left]
              simp only [arr'', Vector.getElem_swap_of_ne (show j' ≠ p by omega) (show j' ≠ i' by omega)]
              simp only [arr', Vector.getElem_swap_right]
              assumption
            )

    else
      move_pivots_back  left right hlr hr p q (by omega)  <|
        if _ : j' < i' then
          ⟨⟨arr, j', i'⟩, by simp only; omega, by simp only; omega, by simp only; omega⟩
        else
          ⟨⟨arr, j' - 1, i' + 1⟩, by simp only; omega, by simp only; omega, by simp only; omega⟩
  -- termination_by j + 1 - i

-- public abbrev Partitioning.Scheme α [Ord α] :=   {n : Nat} → (arr : Vector α n) → (pivot : α) → (left : Nat) → (right : Nat) → (hlr : left < right) → (hr : right < n) →  { x : Partitioning α n  // left < x.i' ∧ x.j' < right }

-- example [Ord α] : Partitioning.Scheme α :=  (@Partitioning.bentleyMcIlroy _ _ _ · · · · · · (halgep :=  sorry) (harltp := sorry))

-- /-- info: { arr' := { toArray := #[4, 3, 1, 0, 5, 2, 6, 8, 7, 9], size_toArray := _ }, j' := 5, i' := 7 } -/
-- #guard_msgs(info) in #eval Partition.bentleyMcIlroy.classic #v[9,  3,  1,  8,  6,  2,  5,  0,  7,  4]  0 9 (by omega) (by omega)

-- /-- info: { arr' := { toArray := #[4, 2, 1, 0, 3, 6, 6, 8, 7, 9], size_toArray := _ }, j' := 4, i' := 7 } -/
-- #guard_msgs(info) in #eval Partition.bentleyMcIlroy.classic #v[9,  3,  1,  8,  6,  2,  6,  0,  7,  4]  0 9 (by omega) (by omega)

-- /-- info: { arr' := { toArray := #[4, 2, 1, 0, 3, 6, 6, 8, 7, 9], size_toArray := _ }, j' := 4, i' := 7 } -/
-- #guard_msgs(info) in #eval Partition.bentleyMcIlroy.classic #v[9,  3,  1,  8,  6,  2,  6,  0,  7,  4]  0 9 (by omega) (by omega)

-- /-- info: { arr' := { toArray := #[0, 0, 0, 1, 2], size_toArray := _ }, j' := 0, i' := 3 } -/
-- #guard_msgs(info) in #eval Partition.bentleyMcIlroy.classic #v[2, 0, 0, 1, 0]  0 4 (by omega) (by omega)
