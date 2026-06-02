module
import Quicksort.Init.Ord

#check lt
open Ord
/--
Restores the max-heap property for a subtree rooted at index `i`.
Operates on a virtual heap mapped between `start` and `start + size` within the vector.
-/
@[specialize]
def heapifyDown [Ord α] (vec : Vector α n) (start size i : Nat) (h_bound : start + size ≤ n) : Vector α n :=
  let left := 2 * i + 1
  let right := left + 1

  if h_left : left < size then
    have hi : start + i < n := by omega
    have hl : start + left < n := by omega

    if h_right : right < size then
      have hr : start + right < n := by omega
      if lt vec[start + i] vec[start + left] then
        if lt vec[start + left] vec[start + right] then
          heapifyDown (vec.swap (start + i) (start + right) hi hr) start size right h_bound
        else
          heapifyDown (vec.swap (start + i) (start + left) hi hl) start size left h_bound
      else
        if lt vec[start + i] vec[start + right] then
          heapifyDown (vec.swap (start + i) (start + right) hi hr) start size right h_bound
        else
          vec
    else
      if lt vec[start + i] vec[start + left] then
        heapifyDown (vec.swap (start + i) (start + left) hi hl) start size left h_bound
      else
        vec
  else
    vec

/--
Sorts a sub-segment of a vector in-place using the Heapsort algorithm.
Guarantees O(N log N) worst-case time complexity, making it an ideal fallback for adversarial inputs.
-/
-- @[noinline]
public def Vector.heapSort (vec : Vector α n) (start : Nat := 0) (endIdx : Nat := n - 1) (h_valid_range : start < endIdx := by omega) (h_bound : endIdx ≤ n - 1 := by omega) [Ord α] : Vector α n :=
  let size := endIdx - start + 1
  -- have h_size : size > 1 := by omega
  have h_upper : start + size ≤ n := by omega

  let rec @[specialize] buildMaxHeap (v : Vector α n) (i : Nat) : Vector α n :=
    let v' := heapifyDown v start size i h_upper
    if i > 0 then buildMaxHeap v' (i - 1) else v'

  let rec @[specialize] extractMax (v : Vector α n) (currentSize : Nat) (h_cur : currentSize ≤ size) : Vector α n :=
    if currentSize > 1 then
      have h1 : start < n := by omega
      have h2 : start + currentSize - 1 < n := by omega

      let v' := v.swap start (start + currentSize - 1) h1 h2
      have h_upper' : start + (currentSize - 1) ≤ n := by omega

      extractMax (heapifyDown v' start (currentSize - 1) 0 h_upper') (currentSize - 1) (by omega)
    else
      v

  extractMax (buildMaxHeap vec (size / 2)) size (by omega)


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


theorem t100 : test_array.size = 100 := by rfl

/--
info: #[0, 0, 0, 1, 3, 3, 3, 4, 4, 4, 5, 6, 7, 8, 10, 11, 13, 14, 14, 14, 16, 17, 18, 19, 24, 24, 24, 25, 26, 27, 29, 29, 30,
  30, 32, 33, 34, 34, 35, 37, 37, 39, 39, 39, 39, 40, 40, 41, 42, 42, 43, 43, 46, 47, 49, 50, 50, 52, 53, 53, 53, 54,
  56, 56, 57, 58, 60, 60, 61, 63, 65, 68, 69, 70, 73, 75, 76, 77, 78, 79, 81, 84, 84, 85, 86, 88, 89, 90, 90, 91, 91,
  91, 91, 93, 94, 95, 95, 96, 99, 99]
-/
#guard_msgs in
#eval Vector.heapSort test_array.toVector 0 99 (by simp) (by grind [t100]) |>.toArray
