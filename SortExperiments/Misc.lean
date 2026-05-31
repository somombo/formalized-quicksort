import SortExperiments.Adapt

namespace PartialQSort
public abbrev Partition.Partial_Scheme α :=  [Ord α] → Array α → Nat → Nat → (Array α × Nat × Nat)

def while_i [Ord α] (pivot : α) (arr : Array α) (ival : Nat) : Nat :=
  have _ : ival < arr.size := sorry
  if compare arr[ival] pivot = .lt then
    while_i pivot arr (ival + 1)
  else
    ival

partial def while_j [Ord α] (pivot : α) (arr : Array α) (jval : Nat) : Nat :=
  have _ : jval < arr.size := sorry
  if compare pivot arr[jval] = .lt then
    while_j pivot arr (jval - 1)
  else
    jval

def maybeSwap [Ord α] (as : Array α) (low high : Fin as.size) : Array α :=
  if compare as[high] as[low] = .lt then
    as.swap low high
  else
    as

namespace PartOne

public partial def partition [Ord α] (arr : Array α) (left : Nat) (right : Nat) : Array α × Nat × Nat :=
  let rec loop (pivot : α) (arr : Array α ) (i j : Nat) :=
    let j' := while_j pivot arr j
    let i' := while_i pivot arr i

    if i' < j' then
      let arr' := arr.swap i' j' sorry sorry
      loop pivot arr' (i' + 1) (j' - 1)
    else
      if j' < i' then
        ⟨arr, j', i'⟩
      else
        ⟨arr, j' - 1, i' + 1⟩

  let mid := left + ((right - left)/2)

  let arr_ := arr
    |> (maybeSwap · ⟨left, sorry⟩ ⟨mid, sorry⟩)
    |> (maybeSwap · ⟨left, sorry⟩ ⟨right, sorry⟩)
    |> (maybeSwap · ⟨mid, sorry⟩ ⟨right, sorry⟩)

  have _ : mid < arr_.size := sorry
  let pivot := arr_[mid]

  loop pivot arr_ (left + 1) (right - 1)

example : Partition.Partial_Scheme α := partition

#guard partition #[9,  3,  1,  8,  6,  2,  5,  0,  7,  4]  0 9
  = (#[4, 3, 1, 0, 5, 2, 6, 8, 7, 9], 5, 6)

#guard partition #[9,  3,  1,  8,  6,  2,  6,  0,  7,  4]  0 9
  = (#[4, 3, 1, 0, 6, 2, 6, 8, 7, 9], 5, 6)

#guard partition #[9,  3,  1,  8,  6,  2,  6,  0,  7,  4]  0 9
  = (#[4, 3, 1, 0, 6, 2, 6, 8, 7, 9], 5, 6)

#guard partition #[2, 0, 0, 1, 0]  0 4
  = (#[0, 0, 0, 1, 2], 1, 2)

end PartOne



namespace PartTwo

def move_pivots_back (left right : Nat) (p q : Nat) (x : Array α × Nat × Nat) : Array α × Nat × Nat :=
  let ⟨arr', j', i'⟩ := x
  let rec move_p_back (k : Nat) (arr : Array α) (j : Nat) : Array α × Nat :=
    if k < p then
      move_p_back (k + 1) (arr.swap k j sorry sorry) (j - 1)
    else
      (arr, j)
  let (arr'', j'') := move_p_back (left + 1) arr' j'

  let rec move_q_forward (k : Nat) (arr : Array α) (i : Nat) : Array α × Nat :=
    if k < right then
      move_q_forward (k + 1) (arr.swap k i sorry sorry) (i + 1)
    else
      (arr, i)
  let (arr''', i'') := move_q_forward (q + 1) arr'' i'

  ⟨arr''', j'', i''⟩

public partial def partition [Ord α] (arr : Array α) (left : Nat) (right : Nat) : Array α × Nat × Nat :=
  let rec loop (pivot : α) (arr : Array α) (i j : Nat) (p q : Nat) :=
    let j' := while_j pivot arr j
    let i' := while_i pivot arr i

    if i' < j' then
      let arr' := arr.swap i' j' sorry sorry
      have _ : i' < arr'.size := sorry
      if compare arr'[i'] pivot = .lt then
        have _ : j' < arr'.size := sorry
        if compare pivot arr'[j'] = .lt then
          loop pivot arr' (i' + 1) (j' - 1) p q
        else
          let arr'' := arr'.swap q j' sorry sorry
          loop pivot arr'' (i' + 1) (j' - 1) p (q - 1)
      else
        let arr'' := arr'.swap p i' sorry sorry

        have _ : j' < arr''.size := sorry
        if compare pivot arr''[j'] = .lt then
          loop pivot arr'' (i' + 1) (j' - 1) (p + 1) q
        else
          let arr''' := arr''.swap q j' sorry sorry
          loop pivot arr''' (i' + 1) (j' - 1) (p + 1) (q - 1)

  else
    move_pivots_back  left right p q <|
      if j' < i' then
        ⟨arr, j', i'⟩
      else
        ⟨arr, j' - 1, i' + 1⟩

  let mid := left + ((right - left)/2)

  let arr_ := arr
    |> (maybeSwap · ⟨left, sorry⟩ ⟨mid, sorry⟩)
    |> (maybeSwap · ⟨left, sorry⟩ ⟨right, sorry⟩)
    |> (maybeSwap · ⟨mid, sorry⟩ ⟨right, sorry⟩)

  have _ : mid < arr_.size := sorry
  let pivot := arr_[mid]

  loop pivot arr_ (left + 1) (right - 1)
    (p := left + 1) (q := right - 1)

example : Partition.Partial_Scheme α := partition

#guard partition #[9,  3,  1,  8,  6,  2,  5,  0,  7,  4]  0 9
  = (#[4, 3, 1, 0, 5, 2, 6, 8, 7, 9], 5, 7)

#guard partition #[9,  3,  1,  8,  6,  2,  6,  0,  7,  4]  0 9
  = (#[4, 2, 1, 0, 3, 6, 6, 8, 7, 9], 4, 7)

#guard partition #[9,  3,  1,  8,  6,  2,  6,  0,  7,  4]  0 9
  = (#[4, 2, 1, 0, 3, 6, 6, 8, 7, 9], 4, 7)

#guard partition #[2, 0, 0, 1, 0]  0 4
  = (#[0, 0, 0, 1, 2], 0, 3)

end PartTwo






public partial def partial_qs [Ord α] (arr : Array α) (left : Nat := 0) (right : Nat := arr.size - 1) (part : Partition.Partial_Scheme α) : Array α :=
  let rec strict (_as : Array α) (_left : Nat) (_right : Nat) : Array α :=
    if _left < _right then
      let ⟨as', j', i'⟩ := part _as _left _right
      let as'' := partial_qs.strict as' _left j'
      let as''' := partial_qs.strict as'' i' _right
      as'''
    else
      _as

  partial_qs.strict arr left right

def test_array := #[
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

def expected_array := #[
  -0, 0, 0, 1, 3, 3, 3, 4, 4, 4, 5, 6, 7,
  8, 10, 11, 13, 14, 14, 14, 16, 17, 18, 19,
  24, 24, 24, 25, 26, 27, 29, 29, 30, 30, 32,
  33, 34, 34, 35, 37, 37, 39, 39, 39, 39, 40,
  40, 41, 42, 42, 43, 43, 46, 47, 49, 50, 50,
  52, 53, 53, 53, 54, 56, 56, 57, 58, 60, 60,
  61, 63, 65, 68, 69, 70, 73, 75, 76, 77, 78,
  79, 81, 84, 84, 85, 86, 88, 89, 90, 90, 91,
  91, 91, 91, 93, 94, 95, 95, 96, 99, 99
]

#guard partial_qs (part := PartOne.partition) test_array = expected_array
#guard partial_qs (part := PartTwo.partition) test_array = expected_array

/--
Sorts an array using an adaptive Quicksort strategy.
Defaults to a fast 2-way Hoare partition, but switches to a 3-way Bentley-McIlroy
partition if too many unbalanced splits are detected. This protects against worst-case
performance on arrays with many duplicate elements.
-/
public partial def adaptive_qs [Ord α] (arr : Array α) (left : Nat := 0) (right : Nat := arr.size - 1) : Array α :=
  let rec strict (_as : Array α) (_left : Nat) (_right : Nat) (allowed_bad_patitions : Nat) : Array α :=
    if _left < _right then
      let len := _right - _left + 1

      let ⟨as', j', i'⟩ :=
        if allowed_bad_patitions > 0 then
          PartOne.partition _as _left _right
        else
          PartTwo.partition _as _left _right

      let left_len := (j' - _left) + 1
      let right_len := (_right - i') + 1

      -- 1/8 (12.5%) is a standard heuristic for imbalance that compiles to a fast bit-shift.
      let unbalanced := left_len < (len / 8) || right_len < (len / 8)

      let next_bad :=
        if unbalanced && allowed_bad_patitions > 0 then
          allowed_bad_patitions - 1
        else
          allowed_bad_patitions

      let as'' := strict as' _left j' next_bad
      let as''' := strict as'' i' _right next_bad
      as'''
    else
      _as

  strict arr left right arr.size.log2


#guard adaptive_qs test_array = expected_array
end PartialQSort







-- -- import Init.Data.Array.Subarray.Split
-- -- import Init.Data.Slice.Array
-- -- import Init.Omega




@[inline]
def qs_adapt_onall [Ord α] (arr : Array α) (left : Nat := 0) (right : Nat := arr.size - 1) (M := 0) (part : Partition.Scheme α ) : Array α :=
  let rec @[specialize]
  strict {n : Nat} (as : Vector α n) (left : Nat := 0) (right : Nat := n - 1) (hsize' : right ≤ n - 1) : Vector α n :=
    if hlr : left + M < right then
      let ⟨⟨as', j', i'⟩, (_ : _ < i'), (_ : j' < _ )⟩ := part as left right (by omega) (by omega)
      let as := qs_adapt_onall.strict as' left j' (by omega)
      let as := qs_adapt_onall.strict as i' right (by omega)
      as
    else
      as
    termination_by right - left

  let right' : Nat := if right ≤ arr.size - 1 then right else
    have := Inhabited.mk (arr.size - 1)
    panic! "index out of bounds"

  have : right' ≤ arr.size - 1 := by
    simp [right']; split <;> simp [panicWithPosWithDecl, panic, panicCore, *]

  Array.insertionSort (qs_adapt_onall.strict ⟨arr, rfl⟩ left right' this).1 (lt := fun a b => (compare a b).isLT)

section introsort
namespace Array

/-- Calculates the base-2 logarithm of a number. -/
private def log2 (n : Nat) : Nat :=
  if n <= 1 then 0 else 1 + log2 (n / 2)

@[macro_inline]
instance foo (lt : α → α → Bool) : Ord α where
  compare a b :=
    if lt a b then .lt
    else if lt b a then .gt
    else .eq


/-- Sorts a small segment of an array using insertion sort. -/
partial def insertionSort' (arr : Array α) (lo : Nat  := 0) (hi : Nat := arr.size - 1) (lt : α → α → Bool  := by exact (· < ·)) : Array α :=
  @Vector.insertionSort α (foo lt) arr.size arr.toVector lo hi sorry |>.1


/-- Restores the heap property for a subtree. -/
private partial def heapifyDown (arr : Array α) (lo hi root : Nat) (lt : α → α → Bool) : Array α :=
  let rec loop (arr : Array α) (current : Nat) : Array α :=
    let left := lo + 2 * (current - lo) + 1
    let right := left + 1
    if left > hi then arr
    else
      let largest := if right <= hi && lt (arr[left]'sorry) (arr[right]'sorry) then right else left
      if lt (arr[current]'sorry) (arr[largest]'sorry) then
        loop (arr.swap current largest sorry sorry) largest
      else arr
  loop arr root

/-- Sorts a segment of an array using heapsort. -/
private partial def heapSort (arr : Array α) (lo hi : Nat) (lt : α → α → Bool) : Array α :=
  let len := hi - lo + 1
  if len <= 1 then arr
  else
    let rec buildHeap (arr : Array α) (i : Nat) : Array α :=
      let arr' := heapifyDown arr lo hi i lt
      if i == lo then arr' else buildHeap arr' (i - 1)
    let arrHeap := buildHeap arr (lo + len / 2 - 1)

    let rec extractAll (arr : Array α) (currentHi : Nat) : Array α :=
      if currentHi <= lo then arr
      else
        let arr' := arr.swap lo currentHi sorry sorry
        extractAll (heapifyDown arr' lo (currentHi - 1) lo lt) (currentHi - 1)
    extractAll arrHeap hi

/-- Partitions a segment of an array around a pivot using the Hoare scheme. -/
private partial def hoarePartition (arr : Array α) (lo hi : Nat) (lt : α → α → Bool) : Nat × Array α :=
  let pivot := arr[lo + (hi - lo) / 2]'sorry
  let rec loop (arr : Array α) (i j : Nat) : Nat × Array α :=
    let rec scanLeft (arr : Array α) (i : Nat) : Nat :=
      if lt (arr[i]'sorry) pivot then scanLeft arr (i + 1) else i
    let rec scanRight (arr : Array α) (j : Nat) : Nat :=
      if lt pivot (arr[j]'sorry) then scanRight arr (j - 1) else j

    let i' := scanLeft arr i
    let j' := scanRight arr j

    if i' >= j' then (j', arr)
    else loop (arr.swap i' j' sorry sorry) (i' + 1) (j' - 1)
  loop arr lo hi

/-- Core recursive loop for introspective sort. -/
private partial def introSortLoop (arr : Array α) (lo hi depthLimit : Nat) (lt : α → α → Bool) : Array α :=
  -- let len := hi - lo + 1
  -- right ≤ left + M
  if hi <= (lo - 1) + 35 then
    @Vector.insertionSort α (foo lt) arr.size ⟨arr, rfl⟩ lo hi sorry |>.1
  else if depthLimit == 0 then
    heapSort arr lo hi lt
  else
    let (p, arr') := hoarePartition arr lo hi lt
    let arr'' := introSortLoop arr' lo p (depthLimit - 1) lt
    introSortLoop arr'' (p + 1) hi (depthLimit - 1) lt

/-- Sorts an array in-place using an optimized introsort algorithm. -/
def introSort (arr : Array α) (lt : α → α → Bool) : Array α :=
  if arr.size <= 1 then arr
  else
    let maxDepth := 2 * log2 arr.size
    introSortLoop arr 0 (arr.size - 1) maxDepth lt

------------- UNIT TESTS ---------------

/-- A collection of test cases to verify the correctness of the sort function. -/

def emptyArray : Array Nat := #[]
#guard introSort emptyArray (· < ·) == #[]

def singleElementArray : Array Nat := #[42]
#guard introSort singleElementArray (· < ·) == #[42]

def alreadySortedArray : Array Nat := #[1, 2, 3, 4, 5]
#guard introSort alreadySortedArray (· < ·) == #[1, 2, 3, 4, 5]

def reverseSortedArray : Array Nat := #[5, 4, 3, 2, 1]
#guard introSort reverseSortedArray (· < ·) == #[1, 2, 3, 4, 5]

def arrayWithDuplicates : Array Nat := #[3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]
#guard introSort arrayWithDuplicates (· < ·) == #[1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9]

def negativeNumbersArray : Array Int := #[3, -1, -4, 1, -5, 9, 2, -6, 5, -3, 5]
#guard introSort negativeNumbersArray (· < ·) == #[-6, -5, -4, -3, -1, 1, 2, 3, 5, 5, 9]

#eval introSort #[10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] (· < ·)


def hello := #[
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


/--
info: #[0, 0, 0, 1, 3, 3, 3, 4, 4, 4, 5, 6, 7, 8, 10, 11, 13, 14, 14, 14, 16, 17, 18, 19, 24, 24, 24, 25, 26, 27, 29, 29, 30,
  30, 32, 33, 34, 34, 35, 37, 37, 39, 39, 39, 39, 40, 40, 41, 42, 42, 43, 43, 46, 47, 49, 50, 50, 52, 53, 53, 53, 54,
  56, 56, 57, 58, 60, 60, 61, 63, 65, 68, 69, 70, 73, 75, 76, 77, 78, 79, 81, 84, 84, 85, 86, 88, 89, 90, 90, 91, 91,
  91, 91, 93, 94, 95, 95, 96, 99, 99]
-/
#guard_msgs in
#eval introSort hello (· < ·)

end Array
end introsort
