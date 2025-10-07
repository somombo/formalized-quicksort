import Bench
import Quicksort.Basic
import Std.Time.DateTime.Timestamp

def exitWithError (msg : String) : IO α := do
  IO.eprintln msg
  IO.Process.exit 1

def parseSizeFromFileName (path : System.FilePath) : IO Nat :=
  let stem : Option String := path.fileStem
  match stem.bind String.toNat? with
  | some size => pure size
  | none => exitWithError s!"Error: Could not parse number from filename '{path}'."

structure Row where
  id : UInt64
  datagen_method : String



def processLine (line : String) (n : Nat) : IO (Row × Array UInt64) := do
  let parts := (line.trim.splitOn ",").toArray
  if parts.size != 3 + n then
    exitWithError s!"Error: Malformed line. Expected {3+n} columns, got {parts.size} in line: '{line}'."

  let id? := parts[0]?.bind (·.toNat?.map UInt64.ofNat)
  let datagen_method? := parts[2]?

  let row ← match (id?, datagen_method?) with
    | (some id, some dm) => pure { id, datagen_method := dm }
    | _ => exitWithError s!"Error: Malformed metadata in line '{line}'."

  let mut numbers := Array.mkEmpty n
  for i in [3:3+n] do
    match parts[i]?.bind (·.toNat?.map UInt64.ofNat) with
    | some num => numbers := numbers.push num
    | none => exitWithError s!"Error: Could not parse number at index {i} in line '{line}'."
  pure (row, numbers)

def getCurrentTimestampString : IO String := do
  let current_time ← Std.Time.ZonedDateTime.now
  return current_time.format "uuuu-MM-dd'T'HH:mm:ssXXX"

def formatMilliseconds (ms : Nat) : String :=
  let minutes := ms / (60 * 1000)
  let remainingMs := ms % (60 * 1000)
  let seconds := remainingMs / 1000
  let milliseconds := remainingMs % 1000
  let msStr := toString milliseconds
  let paddedMsStr := msStr --.leftpad 3 '0'
  s!"{minutes}m{seconds}.{paddedMsStr}s"

def IO.print' [ToString α] (s : α) : IO Unit := do
  let out ← getStdout
  out.putStr <| toString s
  out.flush

def IO.println' [ToString α] (s : α) : IO Unit :=
  print ((toString s).push '\n')

def processFile (inputFile : System.FilePath) (resultsHandle : IO.FS.Handle) : IO Unit := do
  let n ← parseSizeFromFileName inputFile
  let outputDir := System.FilePath.mk "data" / "output"
  let some fileName := inputFile.fileName
    | exitWithError s!"Error: Could not get filename from path '{inputFile}'."
  let outputFile := outputDir / fileName

  let out ← IO.getStdout
  let rec print (s : String) := do
    out.putStr s

  IO.FS.withFile outputFile IO.FS.Mode.append fun outputHandle => do
    IO.FS.withFile inputFile IO.FS.Mode.read fun inputHandle => do
      while true do
        let line ← inputHandle.getLine
        if line.isEmpty then
          break

        let (row, numbers) ← processLine line n
        let timestamp ← getCurrentTimestampString
        IO.print' s!"Benchmark of array with id:={row.id}, time={timestamp}, datagen_method:={row.datagen_method}"

        -- let dataList := numbers.toList
        -- let ⟨dur, dataList⟩ ← timeAx (List.mergeSort <$> pure dataList)
        -- let numbers := dataList.toArray

        let ⟨dur, numbers⟩ ← timeAx (Array.qsort <$> pure numbers); let sort_method := "lean_Array.qsort"

        -- let ⟨dur, numbers⟩ ← timeAx ((qs · (part := Partition.hoare.eager)) <$> pure numbers); let sort_method := "Partition.hoare.eager"
        let sortTimeMs := dur.toMilliseconds

        IO.println' s!", sort_method:=\"{sort_method}\", sortTimeMs := \"{formatMilliseconds sortTimeMs.toInt.toNat}\""
        if n ≤ 10000 then
          let sortedNumbersStr := ",".intercalate (numbers.toList.map toString)
          let outputLine := s!"{row.id},{timestamp},{row.datagen_method},{sortedNumbersStr}"
          outputHandle.putStrLn outputLine
          outputHandle.flush

        let resultsLine := s!"{row.id},{timestamp},{row.datagen_method},{sort_method},{sortTimeMs}"
        resultsHandle.putStrLn resultsLine
        resultsHandle.flush


def main : IO UInt32 := do
  let inputDir := System.FilePath.mk "data" / "input"
  let outputDir := System.FilePath.mk "data" / "output"
  let resultsFile := System.FilePath.mk "data" / "results.csv"

  try
    IO.FS.createDirAll outputDir
    if !(← inputDir.isDir) then
      exitWithError s!"Input directory '{inputDir}' not found."

    IO.FS.withFile resultsFile IO.FS.Mode.append fun resultsHandle => do
      let entries ← inputDir.readDir
      for entry in entries do
        let path := entry.path
        if !(← path.isDir) && path.extension == some "csv" then
          processFile path resultsHandle
    return 0
  catch e =>
    IO.eprintln s!"An unexpected error occurred: {e}"
    return 1
