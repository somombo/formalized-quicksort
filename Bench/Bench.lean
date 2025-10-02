attribute [grind →] Membership.mem.upper -- TODO: somombo) should be added upstream

private def Float.toNatFloor (f : Float) := f.floor.toUSize.toNat
private def Float.toNatCeil (f : Float) := f.ceil.toUSize.toNat

/--
A helper function to shuffle an array. It uses a generalization of the Fisher-Yates algorithm
that can if required perform only a partial shuffle by specifying how many swaps one wants to perform.
For non-maximal swals it progresses in a random order by suffling the indices.
It operates within the IO monad to handle random number generation.
-/
def Array.shuffle {α : Type} (arr : Array α) (swaps := arr.size - 1) : IO (Array α) := do
  if arr.size = 0 ∨ swaps = 0 then return arr

  let idxs := Array.range (arr.size - 1)
  if swaps < arr.size - 1 then
    withIndices $ (←Array.shuffle idxs)[:swaps]
  else
    withIndices idxs

where
  /--
  A helper function to shuffle an array. It uses a generalization of the Fisher-Yates algorithm
  that can if required perform only a partial shuffle by specifying how many swaps one wants to perform.
  It able to progress in a non-linear order by permuting the indices.
  It operates within the IO monad to handle random number generation.
  -/
  withIndices (idxs := Array.range (arr.size - 1)) : IO (Array α) := do
  -- assert! (idxs.size == swaps)
  let mut arr := arr

  let idxs := idxs[:min idxs.size (arr.size - 1)]
  let mut g ← IO.stdGenRef.get
  for i in idxs do
    -- let i' := arr.size - 1 - i
    -- let j' ← IO.rand 0 i'
    let (j, g') := randNat g i (arr.size - 1); g := g'

    -- if idxs.size < arr.size - 1 then println! s!"swaps# {idxs.size}, i: {i}, j: {j}"
    arr := arr.swapIfInBounds i j
  IO.stdGenRef.set g
  return arr


#eval do Array.range 5 |>.shuffle (swaps := 2)


private def Array.toPopulation {α : Type} (counts: Array Nat)
    (populationFn : Fin counts.size → α := by exact fun i => i.1)
    (reverse := false) : Array α := Id.run do
  let mut population := Array.emptyWithCapacity counts.sum
  for _' : i in [:counts.size] do
    let i_ : Fin counts.size := ⟨if reverse then counts.size - 1 - i else i, by grind⟩
    for _ in [:counts[i_]] do population := population.push (populationFn i_)

  return population

def Array.sample {α : Type} (sample_size : Nat) (counts: Array Nat)
    (populationFn : Fin counts.size → α := by exact fun i => i.1)
    (swaps := sample_size - 1) (reverse := false) : IO (Array α) := do
  let as ← counts
    |>.toPopulation (populationFn := populationFn) (reverse := reverse)
    |>.shuffle (swaps := swaps)
  return as |>.extract 0 sample_size



#eval Array.replicate 10 1 |>.sample 5 (swaps := 2)

/--
Generates an array of random natural numbers with specific characteristics
controlled by the following.

- `size`: The desired number of elements in the output array.
- `unique_ratio` determines the variety of elements.
    - unique_ratio = 1.0 -> All elements are unique.
    - unique_ratio = 0.1 -> Elements are drawn from a pool of size * 0.1 numbers.
    - unique_ratio = 0.0 -> All elements are the same (an edge case).
- `swaps_ratio`: A float that determines how many random swaps to perform.
  The number of swaps is (roughly speaking) `(size * swaps_ratio).toNat`.
  - 0.0 means no swaps (perfectly sorted).
  - 1.0 means `size` number of swaps.
- `reverse`: If true, the initial array is sorted in descending order;
  otherwise, it's ascending.

The function operates in the `IO` monad to handle the random number generation.
-/
def Array.randNats (size : Nat) (unique_ratio : Float := 1)
    (swaps_ratio : Float := 1) (reverse := false)
    : IO (Array Nat) := do
  if size = 0 then return #[]

  let swaps := ((size - 1).toFloat * swaps_ratio).toNatCeil
  /- cardinality: the number of unique elements. So 1 ≤ c ≤ s -/
  let card : Float := max 1.0 (min (unique_ratio * size.toFloat) size.toFloat) --

  /- So 1 ≤ d ≤ s -/ -- max 1.0 (min (duplicate_ratio * size.toFloat) size.toFloat)
  let dupes_per_unique : Float := size.toFloat / card

  Array.replicate card.toNatFloor dupes_per_unique.toNatCeil
  |>.sample size
    (swaps := swaps) (reverse := reverse)


/--
Generates an array of random natural numbers where one value is duplicated
many times and other values are unique.

- `size`: The desired number of elements in the output array.
- `duplicate_ratio`: A float between 0.0 and 1.0 that controls the
  proportion of duplicate values. `duplicate_ratio * size` gives the number
  of that are not unique.
- `swaps_ratio`: A float that determines how many random swaps to perform.
  The number of swaps is `(size * swaps_ratio).toNat`.
  - 0.0 means no swaps (initial array is sorted).
  - 1.0 means `size` number of swaps.
- `reverse`: If true, the initial array is sorted in descending order;
  otherwise, it's ascending.

The function operates in the `IO` monad to handle random number generation.
-/
def Array.randNatsWithDominantVal (size : Nat) (duplicate_ratio : Float := 0)
    (swaps_ratio : Float := 1) (reverse := false)
    : IO (Array Nat) := do
  if size = 0 then return #[]

  let swaps := ((size - 1).toFloat * swaps_ratio).toNatCeil
  let dupes_num : Float := max 1.0 (min (duplicate_ratio * size.toFloat) size.toFloat)

  let dupes_num := dupes_num.toNatFloor
  let u := size - dupes_num

  let dominant_val ← IO.rand 0 u

  Array.replicate (u + 1) 1 -- size of this is u + 1
  |>.set! dominant_val dupes_num
  |>.sample size
    (swaps := swaps) (reverse := reverse)



------------------------- TESTS FOR THE ABOVE  ----------------------------

-- Helper function to run a test and print its output neatly.
private def runAndPrint (name : String) (testAction : IO (Array Nat)) : IO Unit := do
  IO.println s!"--- {name} ---"
  let result ← testAction
  IO.println s!"Result: {result}\n"

private def Float.toUniqueRatio (duplicate_ratio : Float) (size : Nat) :=
  1.0/(size.toFloat * duplicate_ratio)

#eval 0.5 |>.toUniqueRatio 1_000_000
#eval 0.5 * 1_000_000
#eval 0.25 |>.toUniqueRatio 1_000_000

#eval do
  -- Example 1: Edge case with size 0.
  runAndPrint "Size 0" $
    Array.randNats 0 (unique_ratio := 1)

#eval do
  -- Example 2: Perfectly sorted (default parameters).
  runAndPrint "Size 10, Sorted, 0% swaps" $
    Array.randNats 10 (unique_ratio := 1) (swaps_ratio := 0)




#eval do
  -- Test 12 of uniques.
  runAndPrint "Size 12, with ceil((12-1)/12)*2 = 2 swaps" $
    Array.randNats 12 (unique_ratio := 1) (swaps_ratio := 2.0/12.0) (reverse := false)

#eval do
  -- Example 3: Perfectly reverse-sorted.
  runAndPrint "Size 10, Reversed, 0% swaps" $
    Array.randNats 10 (unique_ratio := 1) (swaps_ratio := 0) (reverse := true)


#eval do
  -- Example 4: A few swaps on a sorted array.
  -- swap_ratio = 0.2 means ceil(10 * 0.2) = 2 swaps.
  runAndPrint "Size 10, Sorted, 20% swaps (2 swaps)" $
    Array.randNats 10 (unique_ratio := 1) (swaps_ratio := 0.2)

#eval do
  -- Example 5: A few swaps on a reverse-sorted array.
  runAndPrint "Size 10, Reversed, 20% swaps (2 swaps)" $
    Array.randNats 10 (unique_ratio := 1) (swaps_ratio := 0.2) (reverse := true)
#eval do
  -- Example 6: Heavily swapped, almost random.
  -- swap_ratio = 1.0 means floor(10 * 1.0) = 10 swaps.
  runAndPrint "Size 10, Sorted, 100% swaps (10 swaps)" $
    Array.randNats 10 (unique_ratio := 1) (swaps_ratio := 1.0)



---
#eval do
  runAndPrint "Size 10, Low Duplicates (duplicate_ratio := 0.05) so (unique_ratio := 2) which is a complete shuffle" $
    Array.randNats 10 (unique_ratio := 2)

----


#eval do
  runAndPrint "Size 10, (duplicate_ratio := 1.2) so (unique_ratio := 0.083333) effectively All Duplicates" $
    Array.randNats 10 (unique_ratio := 1.0/12)


#eval do
  runAndPrint "Size 20, Medium Duplicates (duplicate_ratio = 0.25). Should be 4 sets of  5 unique values with max value being 3" $
    Array.randNats 20 (unique_ratio := 0.2)



#eval do
  -- Example x: Perfectly sorted with duplicats.
  runAndPrint "Size 10, Sorted, 0% swaps" $
    Array.randNatsWithDominantVal 10 (duplicate_ratio := 0.6) (swaps_ratio := 0)

#eval do
  runAndPrint "Size 20, High Duplicates (duplicate_ratio = 0.8). 16 duplicates, 4 non-duplicates" $
    Array.randNatsWithDominantVal 20 (duplicate_ratio := 0.8)
