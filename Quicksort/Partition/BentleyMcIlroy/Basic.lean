import Quicksort.Partition.Init.Basic

private def dbg {α : Type u} [ToString α] (a : α) (s : String)  : α :=
  dbgTrace s!"{s}" (fun _ => a)

private instance [ToString α] : ToString (Vector α n) where
  toString v := s!"#v{v.toList}"
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
