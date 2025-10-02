
import Quicksort.Basic
import Std.Time.DateTime.Timestamp
import Bench
import Bench.Time
import Batteries.Data.BinaryHeap


-- import Std
import Lean.Data.Json.Parser

def String.toFloat? (s : String) : Option Float :=
  match Lean.Json.parse s with
    | .ok (.num t) => some t.toFloat
    | _ => none

#eval "25.123651".toFloat?



def exitWithError (msg : String) : IO α := do
  IO.eprintln msg
  IO.Process.exit 1

#check Float
def parseNFromFileName (path : System.FilePath) : IO Nat :=
  let stem : Option String := path.fileStem
  match stem.bind String.toNat? with
  | some n => pure n
  | none => exitWithError s!"Error: Could not parse number from filename '{path}'."

structure Row where
  id : UInt64
  unique_frac : Float
  swap_ratio : Float
  reverse : Bool
  size : USize

def stringToBool? (s : String) : Option Bool :=
  if s.toLower == "true" then
    some true
  else if s.toLower == "false" then
    some false
  else
    none


-- #check String.toFloat?
-- #eval (some "55").toNat?.map UInt64.ofNat
def processLine (line : String) (n : Nat) : IO (Row × Array UInt64) := do
  let parts := (line.trim.splitOn ",").toArray
  if parts.size != 6 + n then
    exitWithError s!"Error: Malformed line. Expected {6+n} columns, got {parts.size} in line: '{line}'."

  let id? := (parts.get? 0).bind (·.toNat?.map UInt64.ofNat)
  let unique_frac? := (parts.get? 2).bind String.toFloat?
  let swap_ratio? := (parts.get? 3).bind String.toFloat?
  let reverse? := (parts.get? 4).bind stringToBool?
  let size? := (parts.get? 5).bind String.toNat? |>.map Nat.toUSize

  let row ← match (id?, unique_frac?, swap_ratio?, reverse?, size?) with
    | (some id, some uf, some sr, some r, some s) =>
      if s.toNat != n then
        exitWithError s!"Error: Size column ({s}) does not match filename value ({n})."
      else
        pure { id, unique_frac := uf, swap_ratio := sr, reverse := r, size := s }
    | _ => exitWithError s!"Error: Malformed metadata in line '{line}'."

  let mut numbers := Array.mkEmpty n
  for i in [6:6+n] do
    match (parts.get? i).bind (·.toNat?.map UInt64.ofNat) with
    | some num => numbers := numbers.push num
    | none => exitWithError s!"Error: Could not parse number at index {i} in line '{line}'."
  pure (row, numbers)

def getCurrentTimestampString : IO String := do
  let current_time ← Std.Time.ZonedDateTime.now
  return current_time.format "uuuu-MM-dd'T'HH:mm:ssXXX"

def processFile (inputFile : System.FilePath) (resultsHandle : IO.FS.Handle) : IO Unit := do
  let n ← parseNFromFileName inputFile
  let outputDir := System.FilePath.mk "data" / "output"
  let some fileName := inputFile.fileName
    | exitWithError s!"Error: Could not get filename from path '{inputFile}'."
  let outputFile := outputDir / fileName

  IO.FS.withFile outputFile IO.FS.Mode.append fun outputHandle => do
    IO.FS.withFile inputFile IO.FS.Mode.read fun inputHandle => do
      while true do
        let line ← inputHandle.getLine
        if line.isEmpty then
          break

        let (row, numbers) ← processLine line n
        -- let mut numbers := numbers
        let timestamp ← getCurrentTimestampString

        -- let mut dur : Std.Time.Duration := default
        let ⟨dur, numbers⟩ ← timeAx ((qs · (part := Partition.hoare.eager)) <$> pure numbers)
        let sortTimeMs := dur.toMilliseconds


        let sortedNumbersStr := ",".intercalate (numbers.toList.map toString)
        let outputLine := s!"{row.id},{timestamp},{row.unique_frac},{row.swap_ratio},{row.reverse},{row.size},{sortedNumbersStr}"
        outputHandle.putStrLn outputLine
        outputHandle.flush

        let resultsLine := s!"{row.id},{timestamp},{row.unique_frac},{row.swap_ratio},{row.reverse},{row.size},{sortTimeMs},lean4_hoare_eager_sort"
        resultsHandle.putStrLn resultsLine
        resultsHandle.flush

def main : IO UInt32 := do
  let inputDir := System.FilePath.mk "data" / "input"
  let outputDir := System.FilePath.mk "data" / "output"
  let resultsFile := System.FilePath.mk "data" / "results.csv"

  -- try
  IO.FS.createDirAll outputDir
  if !(← inputDir.isDir) then
    IO.eprintln s!"Input directory '{inputDir}' not found. Skipping processing."
    return 0

  IO.FS.withFile resultsFile IO.FS.Mode.append fun resultsHandle => do
    let entries ← inputDir.readDir
    for entry in entries do
      let path := entry.path
      if !(← path.isDir) then
        processFile path resultsHandle
  -- catch e =>
  --   IO.eprintln s!"An unexpected error occurred: {e}"
  --   return 1
  return 0
