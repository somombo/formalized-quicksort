
import Bench.Time
import Bench


def make_input (size : Nat) (unique_ratio : Float := 1) (swaps_ratio : Float := 1) (reverse := false): IO Unit := do
  if size = 0 then return
  let outDir := System.FilePath.mk "data/input"
  let outFile := outDir / s!"{size}.csv"
  IO.FS.createDirAll outDir
  let handle ← IO.FS.Handle.mk outFile IO.FS.Mode.append


  let data ← Array.randNats size (unique_ratio := unique_ratio) (swaps_ratio := swaps_ratio) (reverse := reverse)
  let data : String := data.extract 1 |>.foldl (· ++ "," ++ toString ·) s!"{data[0]!}"
  let current_time ← Std.Time.ZonedDateTime.now
  let current_time := current_time.format "uuuu-MM-dd'T'HH:mm:ssXXX"
  let data_meta_str := s!"{unique_ratio},{swaps_ratio},{reverse},{size},{data}"
  let id := hash data_meta_str

  handle.putStrLn s!"{id},{current_time},{data_meta_str}"
