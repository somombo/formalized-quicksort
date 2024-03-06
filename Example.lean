import Quicksort

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

#eval qs hello
def arr : Array Int :=  #[2,1,2,3]


-- degenerate
#eval qs (#[] : Array Int)
#eval qs #[0]

-- trivial
#eval qs #[0,1]
#eval qs #[1,0]
#eval qs #[0,0]

-- recursive
#eval qs #[1,2,3]
#eval qs #[3,2,1]
#eval qs #[1,3,2]
#eval qs #[2,1,3]
#eval qs #[3,1,2]
#eval qs #[2,3,1]



#eval qs #[9,  3,  1,  8,  6,  2,  5,  -0,  7,  4]


def main (args : List String) : IO UInt32 := do
  IO.println s!"{qs args.toArray}" -- TODO: implement String instance of LinearOrder for this to work

  -- let mut arr : Array Int := Array.mkEmpty args.length
  -- for i in [:args.length], arg in args do
  --   if let some a := arg.toInt? then
  --     arr := arr.push a
  --   else
  --     IO.println s!"Error: Invalid Input, item[{i}]=\"{arg}\""
  --     return UInt32.ofNatCore (UInt32.size-1) (by decide)

  -- IO.println s!"{qs arr}"

  return 0
