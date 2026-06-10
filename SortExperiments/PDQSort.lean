
module
public meta import Quicksort.Init.BLt
public import SortExperiments.HeapSort
public import SortExperiments.InsertionSort
public import SortExperiments.Partitioning.Hoare
public import SortExperiments.Partitioning.BentleyMcIlroy
import SortExperiments.Pivot.MedianOfThree


open BLt
@[inline]
public def pdqsort [BLt α] [IsStrictWeakOrder α] (arr : Array α) (left : Nat := 0) (right : Nat := arr.size - 1) (M := 0) : Array α :=
  let rec
    @[specialize]
    strict {n : Nat} (as : Vector α n) (left : Nat := 0) (right : Nat := n - 1) (hsize' : right ≤ n - 1)
        (allowed_bad_partitions : Nat := (right - left + 1).log2)
        (has_parent_pivot : Bool := false) : Vector α n :=

      let len := right - left + 1

      if hlr : M + 1 < len then
        if allowed_bad_partitions > 0 then

          have hlr : left < right := by omega
          have hr : right < n := by omega

          let v := Pivot.median_of_three as left right hlr hr
          have : ¬(lt v.piv' v.arr'[left]) ∧ ¬(lt v.arr'[right] v.piv') :=
            Pivot.median_of_three_sorted hlr hr

          let is_duplicate_run : Bool :=
            if has_parent_pivot then
              -- if there is a parent pivot then it has to bel located at position `left - 1`
              eq v.piv' v.arr'[left - 1]
            else
              false


          let ⟨⟨as', j', i'⟩, (_ : left < i'), (_ : j' < right )⟩ :=
            if is_duplicate_run then
              Partitioning.bentleyMcIlroy v.arr' v.piv' left right hlr hr  this.left this.right
            else
              Partitioning.hoare v.arr' v.piv' left right hlr hr  this.left this.right




          let left_len := (j' - left) + 1
          let right_len := (right - i') + 1

          let unbalanced := !is_duplicate_run && (left_len < (len >>> 3) || right_len < (len >>> 3))

          let next_bad_left := if unbalanced then allowed_bad_partitions - 1 else allowed_bad_partitions
          let next_bad_right := if unbalanced then allowed_bad_partitions - 1 else allowed_bad_partitions

          let as''' :=
            if left_len < right_len then
              let as'' := strict as' left j' (by omega) next_bad_left has_parent_pivot
              strict as'' i' right (by omega) next_bad_right true
            else
              let as'' := strict as' i' right (by omega) next_bad_right true
              strict as'' left j' (by omega) next_bad_left has_parent_pivot

          as'''

        else
          as.heapSort left right (by omega) (by omega)
      else
        as.insertionSort left right
      termination_by right - left


  let right' : Nat := if right ≤ arr.size - 1 then right else
    have := Inhabited.mk (arr.size - 1)
    panic! "index out of bounds"

  have : right' ≤ arr.size - 1 := by
    simp [right']; split <;> simp [panicWithPosWithDecl, panic, panicCore, *]

  strict ⟨arr, rfl⟩ left right' this (right' - left + 1).log2 false  |>.1

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


/--
info: #[0, 0, 0, 1, 3, 3, 3, 4, 4, 4, 5, 6, 7, 8, 10, 11, 13, 14, 14, 14, 16, 17, 18, 19, 24, 24, 24, 25, 26, 27, 29, 29, 30,
  30, 32, 33, 34, 34, 35, 37, 37, 39, 39, 39, 39, 40, 40, 41, 42, 42, 43, 43, 46, 47, 49, 50, 50, 52, 53, 53, 53, 54,
  56, 56, 57, 58, 60, 60, 61, 63, 65, 68, 69, 70, 73, 75, 76, 77, 78, 79, 81, 84, 84, 85, 86, 88, 89, 90, 90, 91, 91,
  91, 91, 93, 94, 95, 95, 96, 99, 99]
-/
#guard_msgs in

-- set_option trace.Meta.synthInstance true in
#eval! pdqsort (M := 34) test_array
