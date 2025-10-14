import Quicksort.Partition.Init.Basic

private def dbg {α : Type u} [ToString α] (a : α) (s : String)  : α :=
  dbgTrace s!"{s}" (fun _ => a)

private instance [ToString α] : ToString (Vector α n) where
  toString v := s!"#v{v.toList}"
open Vector






@[inline]
def Partition.bentleyMcIlroy [Inhabited α] /- [ToString α] -/ [Ord α] {n : Nat}
    (arr : Vector α n) (left : Nat)  (right : Nat) (hlr : left < right) (hr : right < n) :
    {x : Partition α n // (left < x.i') ∧ (x.j' < right)} :=


  let rec @[specialize] loop (pivot : α) (arr : Vector α n) (i j p q : Nat) : Vector α n × Nat × Nat × Nat × Nat :=
    let rec @[specialize] findI (i : Nat) :=
      -- i < n
      have right := right
      if /- i < right ∧ -/ lt arr[i]! pivot then
        findI (i + 1)
      else
        i
    termination_by right - i
    decreasing_by sorry

    let rec @[specialize] findJ (j : Nat) :=
      -- 0 < j
      if /- left < j ∧ -/ lt pivot arr[j]! then
        findJ (j - 1)
      else
        j
      termination_by j
      decreasing_by sorry

    let i' := findI (i + 1)
    let j' := findJ (j - 1)

    if i' < j' then Id.run do
      let mut arr := arr.swap i' j' sorry sorry
      let mut p := p
      let mut q := q

      -- if ¬ (lt arr[i]! pivot) ∧ ¬ (lt pivot arr[i]!) then
      if ¬ lt arr[i']! pivot then
        p := p + 1
        arr := arr.swap p i' sorry sorry

      -- if ¬ (lt arr[j]! pivot) ∧ ¬ (lt pivot arr[j]!) then
      if ¬ lt pivot arr[j']! then
        q := q - 1
        arr := arr.swap q j' sorry sorry

      loop pivot arr i' j' p q

    else
      (arr, i', j', p, q)
    termination_by j + 1 - i
    decreasing_by sorry


  let mid := left + (right - left) / 2
  let arr_ := arr
    |> (Vector.maybeSwap . ⟨left, (by omega)⟩ ⟨right, (by omega)⟩)
    |> (Vector.maybeSwap . ⟨mid, (by omega)⟩ ⟨right, (by omega)⟩)
    |> (Vector.maybeSwap . ⟨mid, (by omega)⟩ ⟨left, (by omega)⟩)

  -- let arr := arr.swap left mid (by omega) (by omega)
  let pivot := arr_[left]


  Id.run do
    -- let mut (arr', i', j', p, q) := loop pivot arr_ left (right + 1) left (right + 1)
    let mut (arr', i', j', p, q) := loop pivot arr_ left (right + 1) left (right + 1)

    -- arr := arr.swap left j (sorry) (sorry)
    -- j := j - 1

    for k in [left : p + 1] do
      arr' := arr'.swap k j' sorry sorry
      j' := j' - 1


    for k in [q : right + 1] do
      arr' := arr'.swap k i' sorry sorry
      i' := i' + 1

    return ⟨⟨arr', j', i'⟩, by sorry, by sorry⟩







#eval! Partition.bentleyMcIlroy #v[9,  3,  1,  8,  6,  2,  5,  0,  7,  4]  0 9 (by omega) (by omega)
#eval! Partition.bentleyMcIlroy #v[9,  3,  1,  8,  6,  2,  6,  0,  7,  4]  0 9 (by omega) (by omega)
#eval! Partition.bentleyMcIlroy #v[0, 2, 2, 1, 2]  0 4 (by omega) (by omega)






























-- @[inline]
-- partial def Partition.bentleyMcIlroy [Inhabited α] /-  [BEq α] -/ [ToString α]
--     [Ord α] {n : Nat}
--     (arr : Vector α n) (left : Nat)  (right : Nat) (hlr : left < right) (hr : right < n) :
--     {x : Partition α n // (left < x.i') ∧ (x.j' < right)} := Id.run do
--     -- IO Unit := do
--   let arr := dbg arr s!"arr : {arr}"

--   let mid := left + (right - left) / 2
--   let mut arr := arr
--     |> (maybeSwap · ⟨left, sorry⟩ ⟨mid, sorry⟩)
--     |> (maybeSwap · ⟨left, sorry⟩ ⟨right, sorry⟩)
--     |> (maybeSwap · ⟨mid, sorry⟩ ⟨right, sorry⟩)


--   arr := arr.swap left mid sorry sorry
--   arr := dbg arr s!"arr_: {arr}"

--   let pivot := arr[left]
--   arr := dbg arr s!"pivot: {pivot}"


--   let mut i := left
--   let mut j := right + 1

--   let mut p := left
--   let mut q := right + 1

-- -----------

--   while true do
--     i := i + 1
--     while lt arr[i]! pivot do
--       i := i + 1

--     j := j - 1
--     while lt pivot arr[j]! do
--       j := j - 1

--     if i ≥ j then
--       break

--     arr := arr.swap i j sorry sorry

--     -- if arr[i] == pivot do
--     if ¬ lt arr[i]! pivot then
--       p := p + 1
--       arr := arr.swap p i sorry sorry

--     -- if arr[j] == pivot do
--     if ¬ lt pivot arr[j]! then
--       q := p + 1
--       arr := arr.swap q j sorry sorry


--   arr := arr.swap left j sorry sorry
--   let mut j' := j - 1

--   for k in [left + 1 : p + 1] do
--       arr := arr.swap k j' sorry sorry
--       j' := j' - 1

--   let mut i' := i
--   for k in [q : right + 1] do
--       arr := arr.swap k i' sorry sorry
--       i' := i' + 1



--   return ⟨⟨arr, j', i'⟩, by sorry, by sorry⟩
-- #eval! Partition.bentleyMcIlroy #v[9,  3,  1,  8,  6,  2,  5,  0,  7,  4]  0 9 (by omega) (by omega)



-- #eval! Partition.bentleyMcIlroy #v[9,  3,  1,  8,  6,  2,  6,  0,  7,  4]  0 9 (by omega) (by omega)
-- #eval! Partition.bentleyMcIlroy #v[0, 2, 2, 1, 2]  0 4 (by omega) (by omega)





































-- @[inline]
-- partial def Partition.bentleyMcIlroy [Inhabited α] /-  [BEq α] -/ [ToString α]
--     [Ord α] {n : Nat}
--     (arr : Vector α n) (left : Nat)  (right : Nat) (hlr : left < right) (hr : right < n) :
--     {x : Partition α n // (left < x.i') ∧ (x.j' < right)} := Id.run do
--     -- IO Unit := do
--   let mid := left + (right - left) / 2

--   let arr := dbg arr s!"arr : {arr}"
--   let mut arr := arr
--     |> (maybeSwap · ⟨left, sorry⟩ ⟨mid, sorry⟩)
--     |> (maybeSwap · ⟨left, sorry⟩ ⟨right, sorry⟩)
--     |> (maybeSwap · ⟨mid, sorry⟩ ⟨right, sorry⟩)

--   arr := dbg arr s!"arr_: {arr}"

--   let pivot := arr[mid]!
--   arr := dbg arr s!"pivot: {pivot}"

--   let mut i := left + 1
--   let mut j := right - 1

--   let mut l := left + 1
--   let mut r := right - 1

--   arr := dbg arr s!"l:{l}, i:{i}   ---  {j}:j, {r}:r"
--   let mut count := 0
--   while count < 3 do

--     while i < right ∧ lt arr[i]! pivot do
--       i := i + 1
--       -- if i == right then break

--     while left < j ∧ lt pivot arr[j]! do
--       j := j - 1
--       -- if j == left then break


--     if i ≥ j then --return
--       arr := dbg arr s!"(j, i) := ({j}, {i})"
--       break

--     arr := dbg arr s!"arr1: {arr}, {i}, {j}"
--     arr := arr.swap i j sorry sorry


--     if ¬ lt arr[i]! pivot then
--       arr := dbg arr s!"arri: {arr}, {i}, {l}"
--       arr := arr.swap i l sorry sorry
--       l := l + 1

--     if ¬ lt pivot arr[j]! then
--       arr := dbg arr s!"arrj: {arr}, {j}, {r}"
--       arr := arr.swap j r sorry sorry
--       r := r - 1

--     count := count + 1
--     count := dbg count s!"count := {count}"
--   -- end while
--   arr := dbg arr s!"(j, i) := ({j}, {i})"


--   arr := dbg arr s!"left:  {left},  l: {l}"
--   arr := dbg arr s!"right: {right},  r: {r}"

--   -- arr := arr.swap left j sorry sorry
--   arr := dbg arr s!"arr2: {arr}"
--   -- -- i := i + 1
--   -- j := j - 1
--   for l_ in [left+1:l] do
--     arr := dbg arr s!"larr: {arr}, {l_}, {j}"
--     arr := arr.swap l_ j sorry sorry
--     j := j - 1

--   for r_ in [r+1:right] do
--     arr := dbg arr s!"rarr: {arr}, {r_}, {i}"
--     arr := arr.swap r_ i sorry sorry
--     i := i + 1


--   -- arr := dbg arr $ toString (arr, j, i)
--   return ⟨⟨arr, j, i⟩, by sorry, by sorry⟩

-- -- #eval! Partition.bentleyMcIlroy #v[9,  3,  1,  8,  6,  2,  5,  0,  7,  4]  0 9 (by omega) (by omega)



-- -- #eval! Partition.bentleyMcIlroy #v[9,  3,  1,  8,  6,  2,  6,  0,  7,  4]  0 9 (by omega) (by omega)
-- #eval! Partition.bentleyMcIlroy #v[0, 2, 2, 1, 2]  0 4 (by omega) (by omega)














    -- if ¬lt arr[i]! pivot ∧ ¬lt pivot arr[i]! then
    --   -- panic! "ERROR: arri == piv"
    --   l := l + 1
    --   arr := arr.swap i l sorry sorry

    -- if ¬lt arr[j]! pivot ∧ ¬lt pivot arr[j]! then
    --   -- panic! "ERROR: arrj == piv"
    --   r := r - 1
    --   arr := arr.swap j r sorry sorry









-- @[inline]
-- partial def Partition.bentleyMcIlroy [Inhabited α]  [Ord α] {n : Nat} (arr : Vector α n) (left : Nat)  (right : Nat) (hlr : left < right) (hr : right < n) : {x : Partition α n // (left < x.i') ∧ (x.j' < right)} :=

--   -- let arr_ := arr
--   --   |> (maybeSwap · ⟨left, by omega⟩ ⟨mid, by omega⟩)
--   --   |> (maybeSwap · ⟨left, by omega⟩ ⟨right, by omega⟩)
--   --   |> (maybeSwap · ⟨right, by omega⟩ ⟨mid, by omega⟩)
--   -- have pivot := arr_[right]

--   let mid := left + (right - left) / 2
--   let arr' := arr
--     |> (maybeSwap · ⟨left, sorry⟩ ⟨mid, sorry⟩)
--     |> (maybeSwap · ⟨left, sorry⟩ ⟨right, sorry⟩)
--     |> (maybeSwap · ⟨mid, sorry⟩ ⟨right, sorry⟩)
--   let pivot := arr'[mid]!


--   let rec  scan_i (a : Vector α n) (i : Nat) : Nat :=
--     if i ≤ right ∧ lt a[i]! pivot then
--       scan_i a (i + 1)
--     else
--       i

--   let rec  scan_j (a : Vector α n) (j : Nat) : Nat :=
--     if left ≤ j ∧ lt pivot a[j]! then
--       scan_j a (j - 1)
--     else
--       j


--   let rec main_loop (a : Vector α n) (i j p q : Nat) : Vector α n × Nat × Nat × Nat × Nat :=
--     let i' := scan_i a (i + 1)
--     let j' := scan_j a (j - 1)
--     if i' < j' then
--       let a' := a.swap i' j' sorry sorry
--     -- ¬ lt a'[j']! pivot
--     -- ¬ lt pivot a'[i']!
--       let (a'', p') :=
--         if lt pivot a'[i']! then
--           (a', p)
--         else
--           (a'.swap (p + 1) i' sorry sorry, p + 1)
--       let (a''', q') :=
--         if lt a''[j']! pivot then
--           (a'', q)
--         else
--           (a''.swap (q - 1) j' sorry sorry, q - 1)
--       main_loop a''' i' j' p' q'
--     else
--       (a, i', j', p, q)

--   let (final_arr, i_break, j_break, p_final, q_final) := main_loop arr' (left - 1) (right + 1) left right

--   let rec move_left_eq (a : Vector α n) (k curr_j : Nat) : Vector α n × Nat :=
--     if k > p_final then (a, curr_j)
--     else
--       let a' := a.swap k curr_j sorry sorry
--       move_left_eq a' (k + 1) (curr_j - 1)

--   let rec move_right_eq (a : Vector α n) (k curr_i : Nat) : Vector α n × Nat :=
--     if k < q_final then (a, curr_i)
--     else
--       let a' := a.swap k curr_i sorry sorry
--       move_right_eq a' (k - 1) (curr_i + 1)

--   let (arr_l_done, lt_end) := move_left_eq final_arr left j_break
--   let (arr_r_done, gt_start) := move_right_eq arr_l_done right i_break


--   ⟨⟨arr_r_done, lt_end, gt_start⟩, by sorry, by sorry⟩
-- #eval! Partition.bentleyMcIlroy #v[9,  3,  1,  8,  6,  2,  5,  0,  7,  4]  0 9 (by omega) (by omega)
