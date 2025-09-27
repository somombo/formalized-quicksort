
-- import Std

private def Float.toNatFloor (f : Float) := f.floor.toUSize.toNat
private def Float.toNatCeil (f : Float) := f.ceil.toUSize.toNat

/--
A helper function to shuffle an array. It uses a generalization of the Fisher-Yates algorithm
that can if required perform only a partial shuffle by specifying how many swaps one wants to perform.
It able to progress in a non-linear order by permuting the indices.
It operates within the IO monad to handle random number generation.
-/
def Array.shuffle {α : Type} (arr : Array α) (swaps := arr.size - 1)
    (perm_idxs := Array.range arr.size) : IO (Array α) := do
  let mut arr := arr
  if arr.size = 0 then return #[]

  let swaps := min swaps (arr.size - 1)
  let mut g ← IO.stdGenRef.get
  for i in [0:swaps] do
    let (j, g') := randNat g i (arr.size - 1); g := g'
    -- println! s!"swaps# {swaps}, i: {perm_idxs[i]!}, j: {perm_idxs[j]!}"
    arr := arr.swapIfInBounds perm_idxs[i]! perm_idxs[j]!
    -- let i' := size - 1 - i
    -- let j' ← IO.rand 0 i'
    -- arr := arr.swapIfInBounds perm_idxs[i']! perm_idxs[j']!

  IO.stdGenRef.set g
  return arr



def Array.sample {α : Type} (sample_size : Nat) (counts: Array Nat)
    (populationFn : Fin counts.size → α := by exact fun i => i.1)
    (swaps_ratio : Float := 1) (reverse := false) : IO (Array α) := do

  let swaps := (sample_size.toFloat * swaps_ratio).toNatFloor
  let swaps := min swaps (sample_size - 1)
  let mut population := Array.emptyWithCapacity counts.sum
  let mut i := 0
  while _' : i < counts.size do
    let i_ : Fin counts.size := ⟨if reverse then counts.size - 1 - i else i, by grind⟩
    let freq := counts[i_]
    for _ in [:freq] do population := population.push (populationFn i_)

    i := i + 1

  let idxs ← (Array.range sample_size).shuffle
  return (←(population.shuffle swaps idxs)).extract 0 sample_size



/--
Generates an array of random natural numbers with specific characteristics
controlled by the size and duplicateRatio.

- `size`: The desired number of elements in the output array.
- `duplicate_ratio`: A float between 0.0 and 1.0 (and beyond) that controls
  the proportion of duplicate values in the array.
-/
def Array.mkRandom (size : Nat) (duplicate_ratio : Float := 0)
    (swaps_ratio : Float := 1) (reverse := false)
    : IO (Array Nat) := do
  if size = 0 then
    return #[]

  /- duplicates only, no uniques -/
  if 1 ≤ duplicate_ratio then
    return Array.replicate size 0

  let dupes_num := duplicate_ratio * size.toFloat
  /- no duplicates, uniques only -/
  if dupes_num ≤ 1  then --

    -- Array.range size
    Array.replicate size 1
    |>.sample size
      (swaps_ratio := swaps_ratio) (reverse := reverse)

    -- Array.range size |>.shuffle

  else
  /- two or more uniques (card > 1) -/
  if duplicate_ratio ≤ 0.5 then

    /- cardinality: the (maximum) number of unique elements -/
    let card := (1.0 / duplicate_ratio).toNatFloor

    Array.replicate card dupes_num.toNatCeil
    |>.sample size
      (swaps_ratio := swaps_ratio) (reverse := reverse)

    -- let mut arr := Array.emptyWithCapacity size
    -- for _ in [0:size] do
    --   arr := arr.push (← IO.rand 0 (card - 1))
    -- return arr

  else
    let dupes_num := dupes_num.toNatFloor
    let u := size - dupes_num

    let duplicant ← IO.rand 0 u

    Array.replicate (u + 1) 1 -- size of this is u + 1
    |>.set! duplicant dupes_num
    |>.sample size
      (swaps_ratio := swaps_ratio) (reverse := reverse)


    -- let mut population := Array.emptyWithCapacity size
    -- for i in [:u+1] do
    --   if i == duplicant then
    --     for _ in [:dupes_num] do population := population.push i
    --   else
    --     population := population.push i
    -- Array.shuffle population


/-
Generates an array of a given size that is "almost sorted".

- `size`: The number of elements in the array.
- `swaps_ratio`: A float that determines how many random swaps to perform.
  The number of swaps is `floor(size * swaps_ratio)`.
  - 0.0 means no swaps (perfectly sorted).
  - 1.0 means `size` number of swaps.
- `reverse`: If true, the initial array is sorted in descending order;
  otherwise, it's ascending.

The function operates in the `IO` monad to handle the random number generation.
-/
-- def Array.mkAlmostSorted (size : Nat) (swaps_ratio : Float := 0) (reverse := false) :=
--   Array.mkRandom size (duplicate_ratio := 0) (swaps_ratio := swaps_ratio) (reverse := reverse)

  -- Array.range size
  -- |>.sample size (swaps_ratio := swaps_ratio) (reverse := reverse)
  -- let idxs ← (Array.range arr.size).shuffle

  -- arr.shuffle swaps idxs





------------------------- TESTS FOR THE ABOVE  ----------------------------

-- Helper function to run a test and print its output neatly.
private def runAndPrint (name : String) (testAction : IO (Array Nat)) : IO Unit := do
  IO.println s!"--- {name} ---"
  let result ← testAction
  IO.println s!"Result: {result}\n"




#eval do
  -- Example 1: Edge case with size 0.
  runAndPrint "Size 0" $
    Array.mkRandom 0 (duplicate_ratio := 0)

#eval do
  -- Example 2: Perfectly sorted (default parameters).
  runAndPrint "Size 10, Sorted, 0% swaps" $
    Array.mkRandom 10 (duplicate_ratio := 0) (swaps_ratio := 0)

#eval do
  -- Example x: Perfectly sorted with duplicats.
  runAndPrint "Size 10, Sorted, 0% swaps" $
    Array.mkRandom 10 (duplicate_ratio := 0.6) (swaps_ratio := 0)

#eval do
  -- Example 3: Perfectly reverse-sorted.
  runAndPrint "Size 10, Reversed, 0% swaps" $
    Array.mkRandom 10 (duplicate_ratio := 0) (swaps_ratio := 0) (reverse := true)

#eval do
  -- Example 4: A few swaps on a sorted array.
  -- swap_ratio = 0.2 means floor(10 * 0.2) = 2 swaps.
  runAndPrint "Size 10, Sorted, 20% swaps (2 swaps)" $
    Array.mkRandom 10 (duplicate_ratio := 0) (swaps_ratio := 0.2)

#eval do
  -- Example 5: A few swaps on a reverse-sorted array.
  runAndPrint "Size 10, Reversed, 20% swaps (2 swaps)" $
    Array.mkRandom 10 (duplicate_ratio := 0) (swaps_ratio := 0.2) (reverse := true)
#eval do
  -- Example 6: Heavily swapped, almost random.
  -- swap_ratio = 1.0 means floor(10 * 1.0) = 10 swaps.
  runAndPrint "Size 10, Sorted, 100% swaps (10 swaps)" $
    Array.mkRandom 10 (duplicate_ratio := 0) (swaps_ratio := 1.0)

  -- -- Example 7: More swaps than elements.
  -- -- swap_ratio = 1.5 means floor(10 * 1.5) = 15 swaps.
  -- runAndPrint "Size 10, Sorted, 150% swaps (15 swaps)" $
  --   Array.mkAlmostSorted 10 (swaps_ratio := 1.5)


---
#eval do
  runAndPrint "Size 10, Low Duplicates (effectively a shuffle)" $
    Array.mkRandom 10 (duplicate_ratio := 0.05)

----


#eval do
  runAndPrint "Size 10, All Duplicates" $
    Array.mkRandom 10 (duplicate_ratio := 1.2)

#eval do
  runAndPrint "Size 20, Medium Duplicates (ratio = 0.25). max val be 3" $
    Array.mkRandom 20 (duplicate_ratio := 0.25)

#eval do
  runAndPrint "Size 20, High Duplicates (ratio = 0.8). 16 duplicates, 4 non-duplicates" $
    Array.mkRandom 20 (duplicate_ratio := 0.8)
