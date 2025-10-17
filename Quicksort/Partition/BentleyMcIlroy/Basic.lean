import Quicksort.Partition.Init.Basic
import Quicksort.Utils.RangeHas
import Lean.Elab.Tactic

macro "agemo" : tactic => `(tactic| admit)
private def dbg {α : Type u} [ToString α] (a : α) (s : String)  : α :=
  dbgTrace s!"{s}" (fun _ => a)


private instance [ToString α] : ToString (Vector α n) where
  toString v := s!"#v{v.toList}"

attribute [grind →] Membership.mem.upper
namespace Partition.bentleyMcIlroy.classic
open Vector
variable [Ord α]
instance : Nonempty ([Ord α] → {n j left : Nat} → α → Vector α n → (jval : Nat) → jval ≤ j → left ≤ jval → j < n → { j' // j' ≤ j }) :=
  ⟨fun _ _ jval _ _ _ => ⟨jval, by grind⟩⟩




@[inline]
def loop.while_i' [Ord α] (left right : Nat) (hr : right < n) (pivot : α) (arr : Vector α n) (i j : Nat) (hjr : j < right) /- (harltp : ¬lt arr[right] pivot) -/
  (ival : Nat) (hii : i ≤ ival) (hxi : ival ≤ right) : { i' : Fin n // i ≤ i' ∧ i' ≤ right } :=
  have hi : ival < n := by agemo
  if h' : lt arr[ival] pivot ∧ ival ≤ j then
    -- have _ : ival ≠ right := sorry /- by agemo -/
      -- (h' |> show ¬lt arr[ival] pivot by simpa only [·])
    while_i' left right hr pivot arr i j hjr /- harltp -/   (ival + 1) (by agemo) (by agemo)
  else
    ⟨⟨ival, by agemo⟩, hii, hxi⟩

@[inline]
def loop.while_j' [Ord α] (left right : Nat) (hr : right < n) (hl : left < n) (pivot : α) (arr : Vector α n) (i j : Nat)  (hjr : j < right) (hli : left < i) /- (halgep : ¬lt pivot arr[left]) -/
  (jval : Nat) (hxj : left ≤ jval) (hjj : jval ≤ j) : { j' : Fin n // j' ≤ j } :=
  have hj : jval < n := by agemo
  if h' : lt pivot arr[jval] ∧ i ≤ jval then
    -- have _ : jval ≠ left := sorry /- by agemo -/
      -- (h' |> show ¬lt pivot arr[jval] by simpa only [·])
    while_j' left right hr hl pivot arr i j hjr hli /- halgep -/   (jval - 1) (by agemo) (by agemo)
  else
    ⟨⟨jval, by agemo⟩, hjj⟩
-- partial_fixpoint
-- decreasing_by
--   have hterm_strong_precon : ∃ (left : Nat) (hj' : left < n), left ≤ jval ∧ ¬ lt pivot arr[left] := sorry
--   grind

@[inline]
def _root_.Partition.bentleyMcIlroy.classic [ToString α]  (arr : Vector α n) (left : Nat) (right : Nat)
    (hlr : left < right) (hr : right < n)
    : { x : Partition α n  // left < x.i' ∧ x.j' < right } :=
  have hl : left < n := by agemo
  let mid := left + ((right - left)/2)
  have hm : mid < n := by agemo
  let arr_ := arr |> (maybeSwap · ⟨left, hl⟩ ⟨mid, hm⟩) |> (maybeSwap · ⟨left, hl⟩ ⟨right, hr⟩) |> (maybeSwap · ⟨mid, hm⟩ ⟨right, hr⟩)
  let pivot := arr_[mid]
  let i_ := left + 1; let j_ := right - 1; let p_ := i_; let q_ := j_

  -- let arr_ := dbg arr_ s!"arr1: {arr_},  left: {left}, right: {right}, i': {i_}, j': {j_}, p: {p_}, q: {q_}"
  loop pivot arr_ i_ j_ p_ q_
      (by agemo) (by agemo) (by agemo) (by agemo)  (by agemo) (by agemo)


where


  @[specialize] move_pivots_back (p q : Nat) (hp : p < n) (hq : q  ≤ right - 1) (x : { x : Partition α n  // left < x.i' ∧ x.j' < right ∧ x.i' < n })  :
      { x : Partition α n  // left < x.i' ∧ x.j' < right } :=
    let ⟨⟨arr', j', i'⟩, (_ : left < i'), (_ : j' < right), (_ : i' < n)⟩ := x
    -- let arr' := dbg arr' s!"arr1: {arr'},  left: {left}, right: {right}, i': {i'}, j': {j'}, p: {p}, q: {q}"
    let rec move_p_back (k : Nat) (arr : Vector α n) (j : Nat) (hjr : j < right) (_ : j < right): Vector α n × Subtype (· < right) :=
      if h : k < p then
        move_p_back (k + 1) (arr.swap k j (by agemo) (by agemo)) (j - 1) (by agemo)  (by agemo)
      else
        (arr, ⟨j, by agemo⟩)
    let (arr'', ⟨j'', _⟩) := move_p_back (left + 1) arr' j' (by agemo)  (by agemo)

    let rec move_q_forward (k : Nat) (arr : Vector α n) (i : Nat) (hli : left < i) : Vector α n × Subtype (left < ·) :=
      -- let arr := dbg arr $ if i < n then "" else s!"i: {i}, n: {n}, i < n: {decide (i < n)}"
      if h : k < right then
        move_q_forward (k + 1) (arr.swap k i (by agemo) (by sorry) ) (i + 1) (by agemo)
      else
        (arr, ⟨i, by agemo⟩)


    let (arr''', ⟨i'', _⟩) := move_q_forward (q + 1) arr'' i' (by agemo)

    ⟨⟨arr''', j'', i''⟩, by agemo, by agemo⟩

    -- ⟨⟨arr', j', i'⟩, sorry, sorry⟩

  @[specialize] loop (pivot : α) (arr : Vector α n) (i j : Nat) (p q : Nat)
      (hpi : p ≤ i) (hqr : q < right) (hli : left < i) (hij : i ≤ j + 1) (hjr : j < right)
      (heq_qright : RangeHas n (fun i_ => ¬ lt arr[i_] pivot ∧ ¬ lt pivot arr[i_]) (q + 1) right )
      : { x : Partition α n  // left < x.i' ∧ x.j' < right } :=

    let ⟨⟨j', (_ : j' < n)⟩, (_ : j' ≤ j)⟩  := loop.while_j' left right hr (by agemo) pivot arr i j hjr (by agemo)
      j (by agemo) Nat.le.refl

    let ⟨⟨i', (_ : i' < n)⟩, (_ : i ≤ i'), (_ : i' ≤ right)⟩ := loop.while_i' left right hr pivot arr i j' (by agemo)
      i Nat.le.refl (by agemo)


  -- have : ¬ lt arr[i'] pivot ∨ j < i'
  -- have : arr[i'] ≥ pivot ∨ i' > j'

  -- ¬ lt arr[i'] < pivot
  -- lt arr[i'] < pivot ∨ lt pivot < arr[i']
  -- show i' > j' → arr[i'] > pivot
  -- show i' = j' → arr[i'+1] > pivot




    if _ : i' < j' then
      ----



      let arr' := arr.swap i' j' (by agemo) (by agemo)
      -- loop pivot arr' (i' + 1) (j' - 1) p q (by agemo)  (by agemo)  (by agemo) (by agemo) (by agemo) sorry

      if ha'ipiv : lt arr'[i'] pivot then
        if ha'pivj : lt pivot arr'[j'] then
          -- have : RangeHas n (fun j_ => ¬lt arr'[j_] pivot ∧ ¬lt pivot arr'[j_]) (q + 1) right := by
          --   sorry

          -- have hpi : p ≤ i' + 1 := by agemo
          -- have _ : j' - 1 < q - 1 := by sorry
          -- exact
          loop pivot arr' (i' + 1) (j' - 1) p q (by agemo) (by agemo) (by agemo) (by agemo) (by agemo) sorry
        else
          let arr'' := arr'.swap q j' (by agemo) (by agemo)
          -- have  : RangeHas n (fun j_ => ¬lt arr''[j_] pivot ∧ ¬lt pivot arr''[j_]) (q + 1) right := by
          --   sorry

          -- have hpi : p + 1 ≤ i' + 1 := by agemo
          -- have _ : j' - 1 < q := by sorry
          -- exact
          loop pivot arr'' (i' + 1) (j' - 1) p (q - 1) (by agemo) (by agemo) (by agemo) (by agemo) (by agemo) sorry
      else
        let arr'' := arr'.swap p i' (by agemo) (by agemo)
        if ha'pivj : lt pivot arr''[j'] then

          -- have _ : q - 1 + 1 = q := by sorry
          -- have  : RangeHas n (fun j_ => ¬lt arr''[j_] pivot ∧ ¬lt pivot arr''[j_]) (q - 1 + 1) right := by
          --   sorry

          -- have hpi : p ≤ i' + 1 := by agemo
          -- have hqr' : q - 1 < right := by agemo
          -- have _ : j' - 1 < q - 1 := by sorry
          -- exact
          loop pivot arr'' (i' + 1) (j' - 1) (p + 1) q (by agemo) (by agemo) (by agemo) (by agemo) (by agemo) sorry
        else
          let arr''' := arr''.swap q j' (by agemo) (by agemo)
          -- let arr''' := arr''

          -- have _ : q - 1 + 1 = q := by sorry
          -- have  : RangeHas n (fun j_ => ¬lt arr'''[j_] pivot ∧ ¬lt pivot arr'''[j_]) (q - 1 + 1) right := by
          --   sorry

          -- have hpi : p + 1 ≤ i' + 1 := by agemo
          -- have hqr' : q - 1 < right := by agemo
          -- have _ : j' - 1 < q - 1 := by sorry
          -- exact
          loop pivot arr''' (i' + 1) (j' - 1) (p + 1) (q - 1) (by agemo) (by agemo) (by agemo) (by agemo) (by agemo) sorry

    else
      -- have _ : i' ≤ q  := by sorry
      -- have _ : i' ≤ q + 1 := by sorry
      -- have _ : i' + right - (q + 1) < n := by agemo


      move_pivots_back  p q (by agemo) (by agemo) <|
        if _ : j' < i' then

          ⟨⟨arr, j', i'⟩, by simp only; agemo, by simp only; agemo⟩
        else
          ⟨⟨arr, j' - 1, i' + 1⟩, by simp only; agemo, by simp only; agemo⟩
  termination_by j + 1 - i




  -- termination_by j + 1 - i
  -- decreasing_by
  --   change j' - 1 + 1 - (i' + 1) < j + 1 - i
  --   -- have hii__ : i ≤ i' := sorry
  --   agemo
  -- partial_fixpoint
section
-- set_option warn.sorry false

/-- info: { arr' := { toArray := #[4, 3, 1, 0, 5, 2, 6, 8, 7, 9], size_toArray := _ }, j' := 5, i' := 7 } -/
#guard_msgs(info, drop warning) in #eval! Partition.bentleyMcIlroy.classic #v[9,  3,  1,  8,  6,  2,  5,  0,  7,  4]  0 9 (by agemo) (by agemo)

/-- info: { arr' := { toArray := #[4, 2, 1, 0, 3, 6, 6, 8, 7, 9], size_toArray := _ }, j' := 4, i' := 7 } -/
#guard_msgs(info, drop warning) in #eval! Partition.bentleyMcIlroy.classic #v[9,  3,  1,  8,  6,  2,  6,  0,  7,  4]  0 9 (by agemo) (by agemo)

/-- info: { arr' := { toArray := #[4, 2, 1, 0, 3, 6, 6, 8, 7, 9], size_toArray := _ }, j' := 4, i' := 7 } -/
#guard_msgs(info, drop warning) in #eval! Partition.bentleyMcIlroy.classic #v[9,  3,  1,  8,  6,  2,  6,  0,  7,  4]  0 9 (by agemo) (by agemo)

/-- info: { arr' := { toArray := #[0, 0, 0, 1, 2], size_toArray := _ }, j' := 0, i' := 3 } -/
#guard_msgs(info, drop warning) in #eval! Partition.bentleyMcIlroy.classic #v[2, 0, 0, 1, 0]  0 4 (by agemo) (by agemo)

end
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












      -- ----
      -- let arr' := arr.swap i' j' (by agemo) (by agemo)
      -- let (arr₂, ⟨p', (_ : p' ≤ p + 1)⟩) : Vector α n × Subtype (· ≤ p + 1) :=
      --   if h : ¬ lt arr'[i'] pivot then
      --     (arr'.swap p i' (by agemo) (by agemo), ⟨p + 1, by solve_by_elim⟩)
      --   else
      --     (arr', ⟨p, by solve_by_elim⟩)

      -- let (arr'', ⟨q', (_ : q' < right)⟩) : Vector α n × Subtype (· < right) :=
      --   if h : ¬ lt pivot arr₂[j'] then
      --     (arr₂.swap q j' (by agemo) (by agemo), ⟨q - 1, by agemo⟩)
      --   else
      --     (arr₂, ⟨q, by solve_by_elim⟩)
      -- ---
      -- have  : RangeHas n (fun i_ => ¬lt arr''[i_] pivot = true ∧ ¬lt pivot arr''[i_] = true) (q' + 1) right := by sorry
      -- -- exact
      -- loop pivot arr'' (i' + 1) (j' - 1) p' q' (by agemo)  (by agemo)  (by agemo) (by agemo) (by agemo) this








-- open Vector

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







-- #eval! Partition.bentleyMcIlroy #v[9,  3,  1,  8,  6,  2,  5,  0,  7,  4]  0 9 (by agemo) (by agemo)
-- #eval! Partition.bentleyMcIlroy #v[9,  3,  1,  8,  6,  2,  6,  0,  7,  4]  0 9 (by agemo) (by agemo)
-- #eval! Partition.bentleyMcIlroy #v[9,  3,  1,  8,  6,  2,  6,  0,  7,  4]  0 9 (by agemo) (by agemo)
-- #eval! Partition.bentleyMcIlroy #v[2, 0, 0, 1, 0]  0 4 (by agemo) (by agemo)
