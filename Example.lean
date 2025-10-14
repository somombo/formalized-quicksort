import Quicksort.Basic
-- import Quicksort.Partition.Yaroslavskiy.Basic
-- import Quicksort.Partition.Dutch.Basic
open Partition
------------------------ UNIT TESTS -------------------------------
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

#eval! qs hello (part := hoare)
-- #eval! qs hello (part := Partition.dutch)

/--
info: #[0, 0, 0, 1, 3, 3, 3, 4, 4, 4, 5, 6, 7, 8, 10, 11, 13, 14, 14, 14, 16, 17, 18, 19, 24, 24, 24, 25, 26, 27, 29, 29, 30,
  30, 32, 33, 34, 34, 35, 37, 37, 39, 39, 39, 39, 40, 40, 41, 42, 42, 43, 43, 46, 47, 49, 50, 50, 52, 53, 53, 53, 54,
  56, 56, 57, 58, 60, 60, 61, 63, 65, 68, 69, 70, 73, 75, 76, 77, 78, 79, 81, 84, 84, 85, 86, 88, 89, 90, 90, 91, 91,
  91, 91, 93, 94, 95, 95, 96, 99, 99]
-/
#guard_msgs in
#eval qs hello (part := hoare)
#eval qs hello (part := lomuto)
def arr_example : Array Int :=  #[2,1,2,3]

set_option guard_msgs.diff false

/--
info: #[1, 2, 2, 3]
-/
#guard_msgs(info) in
#eval qs arr_example


-- degenerate
#eval qs (#[] : Array Int)
#eval qs #[0]

-- trivial
#eval! qs #[0,1]
#eval! qs #[1,0]
#eval qs #[0,0]

-- recursive
#eval qs #[1,2,3] -- ()
#eval qs #[1,3,2] -- (23)
#eval qs #[2,1,3] -- (12)
#eval qs #[2,3,1] -- (12)(13)
#eval qs #[3,1,2] -- (12)(23)
#eval qs #[3,2,1] -- (13)

#eval qs #["lorem", "ipsum", "dolor", "sit", "amet"]
  -- Expect: #["amet", "dolor", "ipsum", "lorem", "sit"]

#eval qs.strict (as := #v[9,  3,  1,  8,  6,  2,  5,  -0,  7,  4]) (hsize' := by omega)
#eval! qs #[9,  3,  1,  8,  6,  2,  5,  -0,  7,  4] (part := hoare) (left := 1) (right := 1000) -- EXPECT ERROR: "index out of bounds" with partially sorted output
#eval! qs #[9,  3,  1,  8,  6,  2,  5,  -0,  7,  4] (part := lomuto) (left := 1) (right := 1000) -- EXPECT ERROR: "index out of bounds" with partially sorted output

/- run as ` ./.lake/build/bin/example world hello` -/
def main (args : List String) : IO UInt32 := do
  IO.println s!"{qs args.toArray |>.toList |>.foldl (· ++ " " ++ ·) ""}" -- TODO: implement String instance of LinearOrder for this to work

  -- let mut arr : Array Int := Array.mkEmpty args.length
  -- for i in [:args.length], arg in args do
  --   if let some a := arg.toInt? then
  --     arr := arr.push a
  --   else
  --     IO.println s!"Error: Invalid Input, item[{i}]=\"{arg}\""
  --     return UInt32.ofNatCore (UInt32.size-1) (by decide)

  -- IO.println s!"{qs arr}"

  return 0
