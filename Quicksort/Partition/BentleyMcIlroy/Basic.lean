import Quicksort.Partition.Init.Basic
import Quicksort.Partition.Init.MedianOfThree


-- macro "omega" : tactic => `(tactic| omega)
-- private def dbg {α : Type u} [ToString α] (a : α) (s : String)  : α :=
--   dbgTrace s!"{s}" (fun _ => a)


-- private instance [ToString α] : ToString (Vector α n) where
--   toString v := s!"#v{v.toList}"
open Vector

namespace Partition.bentleyMcIlroy.classic
variable [Ord α]
variable (lt_asymm : ∀ {x y : α}, lt x y → ¬lt y x)
variable (le_trans : ∀ {x y z : α}, ¬lt y x → ¬lt z y → ¬lt z x)
-- instance : Nonempty ([Ord α] → {n j left : Nat} → α → Vector α n → (jval : Nat) → jval ≤ j → left ≤ jval → j < n → { j' // j' ≤ j }) :=
--   ⟨fun _ _ jval _ _ _ => ⟨jval, by grind⟩⟩


def move_pivots_back (left right : Nat) (hlr : left < right) (hr : right < n) (p q : Nat) (hp : p < n)
    (x : { x : Partition α n // left < x.i' ∧ x.j' < right ∧ x.i' ≤ q + 1 }) :
    { x : Partition α n // left < x.i' ∧ x.j' < right } :=
  let ⟨⟨arr', j', i'⟩, (_ : left < i'), (_ : j' < right), (_ : i' ≤ q + 1)⟩ := x
  let rec move_p_back (k : Nat) (arr : Vector α n) (j : Nat) (hjr : j < right) (_ : j < right): Vector α n × Subtype (· < right) :=
    if h : k < p then
      move_p_back (k + 1) (arr.swap k j (by omega) (by omega)) (j - 1) (by omega)  (by omega)
    else
      (arr, ⟨j, by omega⟩)
  let (arr'', ⟨j'', _⟩) := move_p_back (left + 1) arr' j' (by omega)  (by omega)

  let rec move_q_forward (k : Nat) (arr : Vector α n) (i : Nat) (hkq : q + 1 ≤ k) (hli : left < i)
      (hieqk_invar : i = k - (q + 1) + i') : Vector α n × Subtype (left < ·) :=

    if h : k < right then
      move_q_forward (k + 1) (arr.swap k i (by omega) (by omega) ) (i + 1) (by omega) (by omega) (by omega)
    else
      (arr, ⟨i, by omega⟩)


  let (arr''', ⟨i'', _⟩) := move_q_forward (q + 1) arr'' i' (by omega) (by omega) (by omega)

  ⟨⟨arr''', j'', i''⟩, by omega, by omega⟩
@[inline]
def loop.while_j' (left right : Nat) (hr : right < n) (hl : left < n) (pivot : α) (arr : Vector α n) (i j : Nat)  (hjr : j < right) (hli : left < i)
  (jval : Nat) (hxj : left ≤ jval) (hjj : jval ≤ j) (halgep : ¬lt pivot arr[left]) : { j' : Fin n // j' ≤ j ∧ ¬ lt pivot arr[j'.val] } :=
  have hj : jval < n := by omega
  if h' : lt pivot arr[jval] /- ∧ i ≤ jval -/ then
    have _ : jval ≠ left :=
      (h' |> show ¬lt pivot arr[jval] by simpa only [·])
    while_j' left right hr hl pivot arr i j hjr hli    (jval - 1) (by omega) (by omega) halgep
  else
    ⟨⟨jval, by omega⟩, hjj, h'⟩

@[inline]
def loop.while_i'  (left right : Nat) (hr : right < n) (pivot : α) (arr : Vector α n) (i j : Nat) (hjr : j < right)
  (ival : Nat) (hii : i ≤ ival) (hxi : ival ≤ right)
  (harltp : ¬lt arr[right] pivot)
  : { i' : Fin n // i ≤ i' ∧ i' ≤ right ∧  ¬lt arr[i'.val] pivot} :=
  have hi : ival < n := by omega
  if h' : lt arr[ival] pivot then
    have _ : ival ≠ right :=
      (h' |> show ¬lt arr[ival] pivot by simpa only [·])
    while_i' left right hr pivot arr i j hjr    (ival + 1) (by omega) (by omega) harltp
  else
    ⟨⟨ival, by omega⟩, hii, hxi, h'⟩

@[inline]
def _root_.Partition.bentleyMcIlroy.classic [ToString α]  (arr : Vector α n) (left : Nat) (right : Nat)
    (hlr : left < right) (hr : right < n)
    : { x : Partition α n  // left < x.i' ∧ x.j' < right } :=
  have hl : left < n := by omega
  let mid := left + ((right - left)/2)
  have hm : mid < n := by omega
  let arr_ := arr
    |> (maybeSwap · ⟨left, hl⟩ ⟨mid, hm⟩)
    |> (maybeSwap · ⟨left, hl⟩ ⟨right, hr⟩)
    |> (maybeSwap · ⟨mid, hm⟩ ⟨right, hr⟩)
  let pivot := arr_[mid]

  have : ¬lt pivot arr_[left] ∧ ¬lt arr_[right] pivot :=  median_of_three_sorted lt_asymm /- lt_asymm -/ le_trans /- le_trans -/ (by omega) (by omega) hr
  -- let arr_ := dbg arr_ s!"arr1: {arr_},  left: {left}, right: {right}, i': {i_}, j': {j_}, p: {p_}, q: {q_}"
  have hrr : right - 1 + 1 = right := by omega
  have hll : left + 1 - 1 = left := by omega
  loop pivot arr_
    (i := left + 1)
    (j := right - 1)
    (p := left + 1)
    (q := right - 1)
    (by omega) (by omega) (by omega) (by omega)  (by omega) (by omega) (by grind) (by grind)


where
  @[specialize] loop (pivot : α) (arr : Vector α n) (i j : Nat) (p q : Nat)
      (hpi : p ≤ i)  (hqr : q < right) (hli : left < i) (hij : i ≤ j + 1) (hjr : j < right) (hjq : j ≤ q)
      (halgep : ¬lt pivot arr[p - 1]) (haqltp : ¬lt arr[q + 1] pivot)
      : { x : Partition α n  // left < x.i' ∧ x.j' < right } :=

    let ⟨⟨j', (_ : j' < n)⟩, (_ : j' ≤ j), hjpiva⟩  := loop.while_j' (p - 1) right hr (by omega) pivot arr i j hjr (by omega)
      j (by omega) Nat.le.refl halgep
    have hjpiva : ¬lt pivot arr[j'] := hjpiva

    let ⟨⟨i', (_ : i' < n)⟩, (_ : i ≤ i'), (_ : i' ≤ q + 1), hapivi⟩ := loop.while_i' left (q + 1) (by omega) pivot arr i j' (by omega)
      i Nat.le.refl (by omega) (by omega)

    have hapivi : ¬lt arr[i'] pivot := hapivi

    if _ : i' < j' then
      have _ : q - 1 + 1 = q := by omega
      have _ : p + 1 - 1 = p := by omega
      let arr' := arr.swap i' j' (by omega) (by omega)

      -- have : (arr.swap i' j' (by omega) (by omega))[q + 1] = arr[q + 1] := arr.getElem_swap_of_ne (show q + 1 ≠ i' by omega) (show q + 1 ≠ j' by omega)

      if ha'ipiv : lt arr'[i'] pivot then
        if ha'pivj : lt pivot arr'[j'] then by
          have harleq_ : ¬ lt arr'[q + 1] pivot := by
            simp only [arr', arr.getElem_swap_of_ne (show q + 1 ≠ i' by omega) (show q + 1 ≠ j' by omega)]
            assumption
          have halgep' : ¬lt pivot arr'[p - 1] := by
            simp only [arr', arr.getElem_swap_of_ne (show p - 1 ≠ i' by omega) (show p - 1 ≠ j' by omega)]
            assumption
          exact
          loop pivot arr' (i' + 1) (j' - 1) p q (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by grind only) (by grind only)
        else by
          let arr'' := arr'.swap q j' (by omega) (by omega)
          have harleq_ : ¬ lt arr''[q] pivot := by --simpa [arr'', arr']
            simp only [arr'', Vector.getElem_swap_left]
            simp only [arr', Vector.getElem_swap_right]
            assumption

          have halgep' : ¬lt pivot arr''[p - 1] := by
            simp only [arr'', Vector.getElem_swap_of_ne (show p - 1 ≠ q by omega) (show p - 1 ≠ j' by omega)]
            simp only [arr', Vector.getElem_swap_of_ne (show p - 1 ≠ i' by omega) (show p - 1 ≠ j' by omega)]
            assumption

          exact
          loop pivot arr'' (i' + 1) (j' - 1) p (q - 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by grind only) (by grind only)
      else
        let arr'' := arr'.swap p i' (by omega) (by omega)
        if ha'pivj : lt pivot arr''[j'] then by
          have harleq_ : ¬ lt arr''[q + 1] pivot := by
            simp only [arr'', Vector.getElem_swap_of_ne (show q + 1 ≠ p by omega) (show q + 1 ≠ i' by omega)]
            simp only [arr', Vector.getElem_swap_of_ne (show q + 1 ≠ i' by omega) (show q + 1 ≠ j' by omega)]
            assumption

          have halgep' : ¬lt pivot arr''[p] := by --simpa [arr'', arr']
            simp only [arr'', Vector.getElem_swap_left]
            simp only [arr', Vector.getElem_swap_left]
            assumption


          exact
          loop pivot arr'' (i' + 1) (j' - 1) (p + 1) q (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by grind only) (by grind only)
        else by
          let arr''' := arr''.swap q j' (by omega) (by omega)
          have harleq_ : ¬ lt arr'''[q] pivot := by
            simp only [arr''', Vector.getElem_swap_left]
            simp only [arr'', Vector.getElem_swap_of_ne (show j' ≠ p by omega) (show j' ≠ i' by omega)]
            simp only [arr', Vector.getElem_swap_right]
            assumption
          have halgep' : ¬lt pivot arr'''[p] := by
            simp only [arr''', Vector.getElem_swap_of_ne (show p ≠ q by omega) (show p ≠ j' by omega)]
            simp only [arr'', Vector.getElem_swap_left]
            simp only [arr', Vector.getElem_swap_left]
            assumption

          exact
          loop pivot arr''' (i' + 1) (j' - 1) (p + 1) (q - 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by grind only) (by grind only)

    else
      move_pivots_back  left right hlr hr p q (by omega)  <|
        if _ : j' < i' then
          ⟨⟨arr, j', i'⟩, by simp only; omega, by simp only; omega, by simp only; omega⟩
        else
          ⟨⟨arr, j' - 1, i' + 1⟩, by simp only; omega, by simp only; omega, by simp only; omega⟩
  termination_by j + 1 - i





  -- termination_by j + 1 - i
  -- decreasing_by
  --   change j' - 1 + 1 - (i' + 1) < j + 1 - i
  --   -- have hii__ : i ≤ i' := sorry
  --   omega
  -- partial_fixpoint
-- section
-- -- set_option warn.sorry false

-- -- #eval! Partition.bentleyMcIlroy.classic #v[0,0,0,0,0,0,0,0,0]  0 8 (by omega) (by omega)

-- -- #eval! Partition.bentleyMcIlroy.classic #v[0,0,0,0,0,0,0,0,0,0]  0 9 (by omega) (by omega)

-- /-- info: { arr' := { toArray := #[4, 3, 1, 0, 5, 2, 6, 8, 7, 9], size_toArray := _ }, j' := 5, i' := 7 } -/
-- #guard_msgs(info) in #eval! Partition.bentleyMcIlroy.classic #v[9,  3,  1,  8,  6,  2,  5,  0,  7,  4]  0 9 (by omega) (by omega)

-- /-- info: { arr' := { toArray := #[4, 2, 1, 0, 3, 6, 6, 8, 7, 9], size_toArray := _ }, j' := 4, i' := 7 } -/
-- #guard_msgs(info) in #eval! Partition.bentleyMcIlroy.classic #v[9,  3,  1,  8,  6,  2,  6,  0,  7,  4]  0 9 (by omega) (by omega)

-- /-- info: { arr' := { toArray := #[4, 2, 1, 0, 3, 6, 6, 8, 7, 9], size_toArray := _ }, j' := 4, i' := 7 } -/
-- #guard_msgs(info) in #eval! Partition.bentleyMcIlroy.classic #v[9,  3,  1,  8,  6,  2,  6,  0,  7,  4]  0 9 (by omega) (by omega)

-- /-- info: { arr' := { toArray := #[0, 0, 0, 1, 2], size_toArray := _ }, j' := 0, i' := 3 } -/
-- #guard_msgs(info) in #eval! Partition.bentleyMcIlroy.classic #v[2, 0, 0, 1, 0]  0 4 (by omega) (by omega)

-- end
end  Partition.bentleyMcIlroy.classic

-- #where






  -- @[specialize] move_pivots_back (p q : Nat) (x : { x : Partition α n  // left < x.i' ∧ x.j' < right })  :
  --     { x : Partition α n  // left < x.i' ∧ x.j' < right } := Id.run do
  --   let mut ⟨⟨arr', j', i'⟩, (_ : left < i'), (_ : j' < right)⟩ := x
  --   ---
  --   for _' : k in [left + 1 : p] do
  --     arr' := arr'.swap k j' sorry sorry
  --     j' := j' - 1


  --   for _' : k in [q + 1 : right] do
  --     arr' := arr'.swap k i' (by sorry) (by sorry)
  --     i' := i' + 1
  --   ---
  --   return ⟨⟨arr', j', i'⟩, by sorry, by sorry⟩






  -- have : ¬ lt arr[i'] pivot ∨ j < i' (lt pivot arr[i'] ∨ (¬ lt arr[i'] pivot ∧ ¬ lt pivot arr[i']))
  -- have : arr[i'] ≥ pivot ∨ i' > j'

  -- ¬ lt arr[i'] < pivot
  -- lt arr[i'] < pivot ∨ lt pivot < arr[i']
  -- show i' > j' → arr[i'] > pivot
  -- show i' = j' → arr[i'+1] > pivot



  -- ¬ lt pivot arr[j'] ∨ i ≤ j' (lt arr[j'] pivot ∨ (¬ lt pivot arr[j'] ∧ ¬ lt arr[j'] pivot) )






      -- ----
      -- let arr' := arr.swap i' j' (by omega) (by omega)
      -- let (arr₂, ⟨p', (_ : p' ≤ p + 1)⟩) : Vector α n × Subtype (· ≤ p + 1) :=
      --   if h : ¬ lt arr'[i'] pivot then
      --     (arr'.swap p i' (by omega) (by omega), ⟨p + 1, by solve_by_elim⟩)
      --   else
      --     (arr', ⟨p, by solve_by_elim⟩)

      -- let (arr'', ⟨q', (_ : q' < right)⟩) : Vector α n × Subtype (· < right) :=
      --   if h : ¬ lt pivot arr₂[j'] then
      --     (arr₂.swap q j' (by omega) (by omega), ⟨q - 1, by omega⟩)
      --   else
      --     (arr₂, ⟨q, by solve_by_elim⟩)
      -- ---
      -- have  : RangeHas n (fun i_ => ¬lt arr''[i_] pivot = true ∧ ¬lt pivot arr''[i_] = true) (q' + 1) right := by sorry
      -- -- exact
      -- loop pivot arr'' (i' + 1) (j' - 1) p' q' (by omega)  (by omega)  (by omega) (by omega) (by omega) this








-- open Vector
-- attribute [grind →] Membership.mem.upper
-- @[inline]
-- def Partition.bentleyMcIlroy [Inhabited α] /- [ToString α] -/ [Ord α] {n : Nat}
--     (arr : Vector α n) (left : Nat)  (right : Nat) (hlr : left < right) (hr : right < n) :
--     {x : Partition α n // (left < x.i') ∧ (x.j' < right)} := Id.run do

--   let mid := left + (right - left) / 2

--   let mut arr := arr
--     |> (maybeSwap · ⟨left, sorry⟩ ⟨mid, sorry⟩)
--     |> (maybeSwap · ⟨left, sorry⟩ ⟨right, sorry⟩)
--     |> (maybeSwap · ⟨mid, sorry⟩ ⟨right, sorry⟩)

--   let pivot := arr[mid]


--   let mut i := left + 1
--   let mut j := right - 1

--   let mut p := left + 1
--   let mut q := right - 1

--   -- arr := dbg arr s!"arr1: {arr},  left: {left}, right: {right}, i: {i}, j: {j}, p: {p}, q: {q}"
--   while true do

--     while /- i ≠ right ∧ -/ lt arr[i]! pivot do
--       i := i + 1


--     while /- left ≠ j ∧ -/ lt pivot arr[j]! do
--       j := j - 1

--     if i < j then
--       arr := arr.swap i j sorry sorry

--       if ¬ lt arr[i]! pivot then
--         arr := arr.swap p i sorry sorry
--         p := p + 1

--       if ¬ lt pivot arr[j]! then
--         arr := arr.swap q j sorry sorry
--         q := q - 1

--       i := i + 1
--       j := j - 1
--       continue
--     else


--       if j < i then
--         break
--       else
--         i := i + 1
--         j := j - 1

--         break

--   -- arr := dbg arr s!"arr3: {arr},  left: {left}, right: {right}, i: {i}, j: {j}, p: {p}, q: {q}"
--   for k in [left + 1 : p] do
--     arr := arr.swap k j sorry sorry
--     j := j - 1


--   for k in [q + 1 : right] do
--     arr := arr.swap k i sorry sorry
--     i := i + 1

--   return ⟨⟨arr, j, i⟩, by sorry, by sorry⟩







-- #eval! Partition.bentleyMcIlroy #v[9,  3,  1,  8,  6,  2,  5,  0,  7,  4]  0 9 (by omega) (by omega)
-- #eval! Partition.bentleyMcIlroy #v[9,  3,  1,  8,  6,  2,  6,  0,  7,  4]  0 9 (by omega) (by omega)
-- #eval! Partition.bentleyMcIlroy #v[9,  3,  1,  8,  6,  2,  6,  0,  7,  4]  0 9 (by omega) (by omega)
-- #eval! Partition.bentleyMcIlroy #v[2, 0, 0, 1, 0]  0 4 (by omega) (by omega)




@[inline]
def Partition.bentleyMcIlroy.eager [Ord α] {n : Nat} (arr : Vector α n) (left : Nat)  (right : Nat) (hlr : left < right) (hr : right < n) : {x : Partition α n // (left < x.i') ∧ (x.j' < right)} :=
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
