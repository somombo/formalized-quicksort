
import Quicksort.Basic
import Std.Time.DateTime.Timestamp

import Bench
import DataGen.RandomArray
import Batteries.Data.BinaryHeap

/-!
Run for example `lake test -- 10000`
-/

-- (dbgTraceIfShared s!"as={as}\n" as.qsort)


def appendHello ( _ : Unit) : IO Unit := do
  let outDir := System.FilePath.mk "data/input"
  let outFile := outDir / "hello.txt"
  IO.FS.createDirAll outDir
  let handle ← IO.FS.Handle.mk outFile IO.FS.Mode.append
  handle.putStr "Hello world"


def bench (name : String) (data : Array Nat): IO Unit := do
  IO.println s!"\n{name}:"

  let ⟨dur, _⟩ ← timeAx ((qs · (part := Partition.hoare.eager)) <$> pure data)
  IO.println s!"  Partition.hoare.eager: {dur.toMilliseconds}ms"

  let ⟨dur, _⟩ ← timeAx ((qs · (part := Partition.hoare.new)) <$> pure data)
  IO.println s!"  Partition.hoare.new:   {dur.toMilliseconds}ms"

  let ⟨dur, _⟩ ← timeAx (Array.insertionSort <$> pure data)
  IO.println s!"  Array.insertionSort:   {dur.toMilliseconds}ms"

  let dataList := data.toList
  let ⟨dur, _⟩ ← timeAx (List.mergeSort <$> pure dataList)
  IO.println s!"  List.mergeSort:        {dur.toMilliseconds}ms"

  let ⟨dur, _⟩ ← timeAx ((qs · (part := Partition.lomuto)) <$> pure data)
  IO.println s!"  Partition.lomuto:      {dur.toMilliseconds}ms"

  let ⟨dur, _⟩ ← timeAx ((Array.heapSort · (· < ·))  <$> pure data)
  IO.println s!"  Array.heapSort:        {dur.toMilliseconds}ms"

  let ⟨dur, _⟩ ← timeAx (Array.qsort <$> pure data)
  IO.println s!"  Array.qsort:           {dur.toMilliseconds}ms"

  IO.println ""

def main (args : List String): IO Unit := do
  let some arg := args[0]? | throw <| IO.userError s!"specify size test array"
  let some size := arg.toNat? | throw <| IO.userError s!"specify size test array"


  let data ← Array.randNats size (swaps_ratio := 0) -- (unique_ratio := 1)
  let _ ← bench "Sorted Uniques" data

  let data ← Array.randNats size (swaps_ratio := 0.0001) -- (unique_ratio := 1) (swaps_ratio := 1)
  let _ ← bench "Almost Sorted Uniques" data

  let data ← Array.randNats size (swaps_ratio := 0) (reverse := true) -- (unique_ratio := 1)
  let _ ← bench "Reverse Sorted Uniques" data

  let data ← Array.randNats size -- (unique_ratio := 1) (swaps_ratio := 1)
  let _ ← bench "Unsorted Uniques" data

  let data ← Array.randNats size (unique_ratio := 0.25) -- (swaps_ratio := 1)
  let _ ← bench "High Duplicates" data

  let data ← Array.randNats size (unique_ratio := 0.5) -- (swaps_ratio := 1)
  let _ ← bench "Mid Duplicates" data

  let data ← Array.randNats size (unique_ratio := 0) (swaps_ratio := 0)
  let _ ← bench "All Duplicates" data


#eval do main ["500"]
-- --------------

--   let data ← Array.randNatsWithDominantVal size (duplicate_ratio := 0.6) (swaps_ratio := 0)
--   let _ ← bench "Sorted With Duplicates" data

--   let data ← Array.randNatsWithDominantVal size (duplicate_ratio := 0.9)
--   let _ ← bench "Very High Duplicates" data











-- def main2 (args : List String) : IO Unit := do
--   -- let size := 5000000
--   let some arg := args[0]? | throw <| IO.userError s!"specify size test array"
--   let some size := arg.toNat? | throw <| IO.userError s!"specify size test array"

--   IO.println s!"Generating a random array of size {size}..."

--   -- Generate a highly unsorted array to give qsort some real work to do.
--   -- let unsortedArr ← Array.mkAlmostSorted size (swaps_ratio := 0.9)
--   let unsortedArr ← Array.randNats size (duplicateRatio := 0.9)
--   let unsortedArr_copy := Array.mk unsortedArr.toList
--   IO.println "Generation complete. Starting timer and sorting..."
--   IO.println "------------------------------------------------"

--   -- 1. Get the start time. `←` unwraps the Nat from the IO action.
--   IO.println s!"First 5 elements of unsorted array: {unsortedArr_copy.extract 0 5}"
--   let startTime ← Std.Time.Timestamp.now

--   -- 2. Perform the expensive computation.
--   -- Note: `qsort` is a pure function. It returns a NEW sorted array.
--   -- We must assign its result to a variable.
--   let sortedArr := (qs unsortedArr_copy (part := Partition.hoare.new))


--   -- 3. Calculate and report the duration.
--   let duration ← Std.Time.Timestamp.since startTime

--   IO.println s!"Array has been sorted."
--   IO.println s!"First 5 elements of sorted array: {sortedArr.extract 0 5}"
--   IO.println s!"✅ Hoare Sorting took {duration.toMilliseconds}ms"
--   IO.println "------------------------------------------------"
