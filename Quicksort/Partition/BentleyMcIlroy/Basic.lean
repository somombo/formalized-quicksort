import Quicksort.Partition.Init.Basic


private def dbg {α : Type u} [ToString α] (a : α) (s : String)  : α :=
  dbgTrace s!"{s}" (fun _ => a)

private instance [ToString α] : ToString (Vector α n) where
  toString v := s!"#v{v.toList}"

attribute [grind →] Membership.mem.upper
namespace Partition.bentleyMcIlroy.eagar
open Vector
variable [Ord α]
instance : Nonempty ([Ord α] → {n j left : Nat} → α → Vector α n → (jval : Nat) → jval ≤ j → left ≤ jval → j < n → { j' // j' ≤ j }) :=
  ⟨fun _ _ jval _ _ _ => ⟨jval, by grind⟩⟩



@[inline]
def loop.while_i' [Ord α] (left right : Nat) (hr : right < n) (pivot : α) (arr : Vector α n) (i j : Nat) (hjr : j < right) /- (harltp : ¬lt arr[right] pivot) -/
  (ival : Nat) (hii : i ≤ ival) (hxi : ival ≤ right) : { i' : Fin n // i ≤ i' ∧ i' ≤ right } :=
  have hi : ival < n := by omega
  if h' : lt arr[ival] pivot ∧ ival ≤ j then
    -- have _ : ival ≠ right := sorry /- by omega -/
      -- (h' |> show ¬lt arr[ival] pivot by simpa only [·])
    while_i' left right hr pivot arr i j hjr /- harltp -/   (ival + 1) (by omega) (by omega)
  else
    ⟨⟨ival, by omega⟩, hii, hxi⟩

@[inline]
def loop.while_j' [Ord α] (left right : Nat) (hr : right < n) (hl : left < n) (pivot : α) (arr : Vector α n) (i j : Nat)  (hjr : j < right) (hli : left < i) /- (halgep : ¬lt pivot arr[left]) -/
  (jval : Nat) (hxj : left ≤ jval) (hjj : jval ≤ j) : { j' : Fin n // j' ≤ j } :=
  have hj : jval < n := by omega
  if h' : lt pivot arr[jval] ∧ i ≤ jval then
    -- have _ : jval ≠ left := sorry /- by omega -/
      -- (h' |> show ¬lt pivot arr[jval] by simpa only [·])
    while_j' left right hr hl pivot arr i j hjr hli /- halgep -/   (jval - 1) (by omega) (by omega)
  else
    ⟨⟨jval, by omega⟩, hjj⟩
-- partial_fixpoint
-- decreasing_by
--   have hterm_strong_precon : ∃ (left : Nat) (hj' : left < n), left ≤ jval ∧ ¬ lt pivot arr[left] := sorry
--   grind

@[inline]
def _root_.Partition.bentleyMcIlroy.classic (arr : Vector α n) (left : Nat) (right : Nat)
    (hlr : left < right)
    (hr : right < n) : { x : Partition α n  // left < x.i' ∧ x.j' < right } :=
  have hl : left < n := by omega
  let mid := left + ((right - left)/2)
  have hm : mid < n := by omega
  let arr_ := arr
    |> (maybeSwap · ⟨left, hl⟩ ⟨mid, hm⟩)
    |> (maybeSwap · ⟨left, hl⟩ ⟨right, hr⟩)
    |> (maybeSwap · ⟨mid, hm⟩ ⟨right, hr⟩)

  let pivot := arr_[mid]

  let i_ := left + 1
  let j_ := right - 1

  let p_ := i_
  let q_ := j_

  -- let arr_ := dbg arr_ s!"arr1: {arr_},  left: {left}, right: {right}, i': {i_}, j': {j_}, p: {p_}, q: {q_}"
  loop pivot arr_ i_ j_ p_ q_
      (by omega) (by omega) (by omega) (by omega)  (by omega)


where
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


  @[specialize] move_pivots_back (p q : Nat) (hp : p < n) (hq : q  ≤ right - 1) (x : { x : Partition α n  // left < x.i' ∧ x.j' < right ∧ x.i' < n })  :
      { x : Partition α n  // left < x.i' ∧ x.j' < right } :=
    let ⟨⟨arr', j', i'⟩, (_ : left < i'), (_ : j' < right), (_ : i' < n)⟩ := x

    let rec move_p_back (k : Nat) (arr : Vector α n) (j : Nat) (hjr : j < right) (_ : j < right): Vector α n × Subtype (· < right) :=
      if h : k < p then
        move_p_back (k + 1) (arr.swap k j (by omega) (by omega)) (j - 1) (by omega)  (by omega)
      else
        (arr, ⟨j, by omega⟩)
    let (arr'', ⟨j'', _⟩) := move_p_back (left + 1) arr' j' (by omega)  (by omega)

    let rec move_q_forward (k : Nat) (arr : Vector α n) (i : Nat) (hli : left < i) : Vector α n × Subtype (left < ·) :=
      if h : k < right then
        move_q_forward (k + 1) (arr.swap k i (by omega) (by sorry) ) (i + 1) (by omega)
      else
        (arr, ⟨i, by omega⟩)


    let (arr''', ⟨i'', _⟩) := move_q_forward (q + 1) arr'' i' (by omega)

    ⟨⟨arr''', j'', i''⟩, by constructor; all_goals assumption⟩

  @[specialize] loop (pivot : α) (arr : Vector α n) (i j : Nat) (p q : Nat) (hpi : p ≤ i) (hqr : q < right)

      (hli : left < i) (hij : i ≤ j + 1) (hjr : j < right) :
      { x : Partition α n  // left < x.i' ∧ x.j' < right } :=


    let ⟨⟨i', _⟩, _, _⟩ := loop.while_i' left right hr pivot arr i j (by omega)
      i Nat.le.refl (by omega)



    let ⟨⟨j', _⟩, _⟩  := loop.while_j' left right hr (by omega) pivot arr i' j hjr (by grind)
      j (by omega) Nat.le.refl


    if _ : i' < j' then
      let arr' := arr.swap i' j' (by omega) (by omega)
      ----
      let (arr₂, ⟨p', _⟩) : Vector α n × Subtype (· ≤ p + 1) :=
        if h : ¬ lt arr'[i'] pivot then
          (arr'.swap p i' (by omega) (by omega), ⟨p + 1, by solve_by_elim⟩)
        else
          (arr', ⟨p, by solve_by_elim⟩)

      let (arr'', ⟨q', _⟩) : Vector α n × Subtype (· < right) :=
        if h : ¬ lt pivot arr₂[j'] then
          (arr₂.swap q j' (by omega) (by omega), ⟨q - 1, by omega⟩)
        else
          (arr₂, ⟨q, by solve_by_elim⟩)
      ---
      loop pivot arr'' (i' + 1) (j' - 1) p' q' (by grind)  (by grind) (by grind) (by grind) (by grind)
    else
      move_pivots_back  p q (by omega) (by omega) <|
        if _ : j' < i' then

          ⟨⟨arr, j', i'⟩, by grind⟩
        else
          ⟨⟨arr, j' - 1, i' + 1⟩, by grind⟩
  termination_by j + 1 - i
  decreasing_by grind




  -- termination_by j + 1 - i
  -- decreasing_by
  --   change j' - 1 + 1 - (i' + 1) < j + 1 - i
  --   -- have hii__ : i ≤ i' := sorry
  --   omega
  -- partial_fixpoint

#eval! _root_.Partition.bentleyMcIlroy.classic #v[9,  3,  1,  8,  6,  2,  5,  0,  7,  4]  0 9 (by omega) (by omega)
#eval! _root_.Partition.bentleyMcIlroy.classic #v[9,  3,  1,  8,  6,  2,  6,  0,  7,  4]  0 9 (by omega) (by omega)
#eval! _root_.Partition.bentleyMcIlroy.classic #v[9,  3,  1,  8,  6,  2,  6,  0,  7,  4]  0 9 (by omega) (by omega)
#eval! _root_.Partition.bentleyMcIlroy.classic #v[2, 0, 0, 1, 0]  0 4 (by omega) (by omega)

end  Partition.bentleyMcIlroy.eagar





    -- have _ : i' ≤ q + 1 := by sorry
    -- have _ : i' + right - (q + 1) < n := by omega








open Vector

@[inline]
def Partition.bentleyMcIlroy [Inhabited α] /- [ToString α] -/ [Ord α] {n : Nat}
    (arr : Vector α n) (left : Nat)  (right : Nat) (hlr : left < right) (hr : right < n) :
    {x : Partition α n // (left < x.i') ∧ (x.j' < right)} := Id.run do

  let mid := left + (right - left) / 2

  let mut arr := arr
    |> (maybeSwap · ⟨left, sorry⟩ ⟨mid, sorry⟩)
    |> (maybeSwap · ⟨left, sorry⟩ ⟨right, sorry⟩)
    |> (maybeSwap · ⟨mid, sorry⟩ ⟨right, sorry⟩)

  let pivot := arr[mid]


  let mut i := left + 1
  let mut j := right - 1

  let mut p := left + 1
  let mut q := right - 1

  -- arr := dbg arr s!"arr1: {arr},  left: {left}, right: {right}, i: {i}, j: {j}, p: {p}, q: {q}"
  while true do

    while /- i ≠ right ∧ -/ lt arr[i]! pivot do
      i := i + 1


    while /- left ≠ j ∧ -/ lt pivot arr[j]! do
      j := j - 1

    if i < j then
      arr := arr.swap i j sorry sorry

      if ¬ lt arr[i]! pivot then
        arr := arr.swap p i sorry sorry
        p := p + 1

      if ¬ lt pivot arr[j]! then
        arr := arr.swap q j sorry sorry
        q := q - 1

      i := i + 1
      j := j - 1
      continue
    else


      if j < i then
        break
      else
        i := i + 1
        j := j - 1

        break

  -- arr := dbg arr s!"arr3: {arr},  left: {left}, right: {right}, i: {i}, j: {j}, p: {p}, q: {q}"
  for k in [left + 1 : p] do
    arr := arr.swap k j sorry sorry
    j := j - 1


  for k in [q + 1 : right] do
    arr := arr.swap k i sorry sorry
    i := i + 1

  return ⟨⟨arr, j, i⟩, by sorry, by sorry⟩







#eval! Partition.bentleyMcIlroy #v[9,  3,  1,  8,  6,  2,  5,  0,  7,  4]  0 9 (by omega) (by omega)
#eval! Partition.bentleyMcIlroy #v[9,  3,  1,  8,  6,  2,  6,  0,  7,  4]  0 9 (by omega) (by omega)
#eval! Partition.bentleyMcIlroy #v[9,  3,  1,  8,  6,  2,  6,  0,  7,  4]  0 9 (by omega) (by omega)
#eval! Partition.bentleyMcIlroy #v[2, 0, 0, 1, 0]  0 4 (by omega) (by omega)
