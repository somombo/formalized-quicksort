import Bench.Time
import Bench

import Quicksort.Basic
import Batteries.Data.BinaryHeap


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

#check IO.FS.Handle
def appendHello ( _ : Unit) : IO Unit := do
  let outDir := System.FilePath.mk "data/input"
  let outFile := outDir / "hello.txt"
  IO.FS.createDirAll outDir
  let handle ← IO.FS.Handle.mk outFile IO.FS.Mode.append
  handle.putStr "Hello world"





-- #eval appendHello ()
