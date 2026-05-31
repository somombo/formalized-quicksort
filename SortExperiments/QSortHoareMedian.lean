

module
public import  SortExperiments.Partitioning.Hoare
public import SortExperiments.InsertionSort
public import SortExperiments.Pivot.Median
import Quicksort.Init.Ord

variable
  [Ord α]
  -- [ile_trans : Std.TransOrd α]


open Ord

@[inline]
public def qsort_hoare_median (arr : Array α) /- (left : Nat := 0) -/ /- (right := arr.size - 1) -/ (M := 32) (hM : M > 0 := by omega)
    (not_lt : ∀ {x y : α}, ¬(compare y x |>.isLT) ↔ (compare x y |>.isLE) := by grind)
    (le_trans : ∀ {x y z : α}, (compare x y).isLE → (compare y z).isLE → (compare x z).isLE := by grind)
    : Array α :=
  let rec @[specialize]
  recurse {n} (as : Vector α n) (left : Nat) (right: Nat) (hsize' : right ≤ n - 1) : Vector α n :=
    if hlr : left + M < right then
      have hr : right < n := by omega
      have hlr : left < right  := by omega
      let v := Pivot.median (M := M) as left right hlr hr
      have : ¬(compare v.piv' v.arr'[left] |>.isLT) ∧ ¬(compare v.arr'[right] v.piv' |>.isLT) :=
        Pivot.median_sorted (M:=M) (hM : M > 0) not_lt le_trans hlr hr


      let ⟨⟨a, j', i'⟩, (_ : _ < i'), (_ : j' < _ )⟩ :=
        Partitioning.hoare v.arr' v.piv' left right hlr hr  this.left this.right

      recurse a left j' (by omega)
      |>
      (recurse · i' right (by omega))
    else
      as.insertionSort left right
    termination_by right - left

  recurse ⟨arr, rfl⟩ 0 (arr.size - 1) (by omega) |>.1



/--
info: #[0, 0, 0, 1, 3, 3, 3, 4, 4, 4, 5, 6, 7, 8, 10, 11, 13, 14, 14, 14, 16, 17, 18, 19, 24, 24, 24, 25, 26, 27, 29, 29, 30,
  30, 32, 33, 34, 34, 35, 37, 37, 39, 39, 39, 39, 40, 40, 41, 42, 42, 43, 43, 46, 47, 49, 50, 50, 52, 53, 53, 53, 54,
  56, 56, 57, 58, 60, 60, 61, 63, 65, 68, 69, 70, 73, 75, 76, 77, 78, 79, 81, 84, 84, 85, 86, 88, 89, 90, 90, 91, 91,
  91, 91, 93, 94, 95, 95, 96, 99, 99]
-/
#guard_msgs in
#eval! qsort_hoare_median #[
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


-- def main (args : List String) : IO UInt32 := do
--   let out := qsort_hoare_mo3 args.toArray
--   IO.println s!"{out}"
--   return 0

-- #eval main ["momo", "somo", "aaa"]
