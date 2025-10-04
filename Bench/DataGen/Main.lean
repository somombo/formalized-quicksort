
import DataGen.RandomArray
import Std.Time
import Cli
import Lean.Data.Json.Parser

def String.toFloat? (s : String) : Option Float :=
  match Lean.Json.parse s with
    | .ok (.num t) => some t.toFloat
    | _ => none


instance : Cli.ParseableType Float where
  name := "Float"
  parse?
    | "" => none
    | s  => s.toFloat?


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
  let datagen_method := s!"{unique_ratio}:{swaps_ratio}:{reverse}:{size}"
  let id := hash data

  handle.putStrLn s!"{id},{current_time},{datagen_method},{data}"

open Cli

def main (args : List String) : IO UInt32 := Cmd.validate (args:=args)
$ (fun run => `[Cli|
  datagen VIA run; --["0.0.1"]
  "The datagen command generates the arrays to be tested"
  FLAGS:
    u, "unique-ratio" : Array Float;      "--unique-ratio description"
    s, "swaps-ratio" : Array Float;       "--swaps-ratio description"
    r, reverse;                     "--reverse description"
    f, forward;                     "--forward opposite of reverse"

  ARGS:
    size : Nat;                     "the array size"
    ...sizes : Nat;                     "the array size"

  EXTENSIONS:
    defaultValues! #[("unique-ratio", "1"), ("swaps-ratio", "1")]
])
$ (fun p => do
  let some size := p.positionalArg? "size" | throw$ IO.userError s!"specify size test array"
  let some size := size.as? Nat | throw$ IO.userError s!"`size` must be a valid natural number"

  let sizes : Array Nat := p.variableArgsAs! Nat

  let unique_ratios := p.flag! "unique-ratio" |>.as! (Array Float)
  let swaps_ratios := p.flag! "swaps-ratio" |>.as! (Array Float)
  -- let reverses := p.flag! "reverse" |>.as! (Array Bool)
  -- let reverse := p.flag? "reverse" |>.isSome

  let reverses :=
    match (p.flag? "reverse", p.flag? "forward") with
    | ⟨some _, some _⟩ => [true,false]
    | ⟨some _, none⟩ => [true]
    | ⟨none, _⟩ => [false]

  let mut count := 0
  for size in (size :: sizes.toList) do
    for reverse in reverses do
      for swaps_ratio in swaps_ratios do
        for unique_ratio in unique_ratios do
          let _ ← make_input size
            (unique_ratio := unique_ratio)
            (swaps_ratio := swaps_ratio)
            (reverse := reverse)
          println! s!"Done Generating data with (size := {size}) /
          (unique_ratio := {unique_ratio}) (swaps_ratio := {swaps_ratio}) /
          (reverse := {reverse})"
          count := count + 1
  println! s!"Added {count} to the dataset"




  return default
)

-- #eval main $ "--unique-ratio=0.1,0.25,0.5,0.75,0.9,1 --swaps-ratio=0,0.001,0.01,0.05,0.1,0.5 --reverse --forward 100"            |>.splitOn " "
-- #eval main $ "--unique-ratio=0,0.1,0.25,0.5,0.75,0.9,1,1 100"            |>.splitOn " "




























-- #eval main $ "--unique-ratio=0 --swaps-ratio=0 100"            |>.splitOn " "
-- #eval main $ "--unique-ratio=0.1,0.25,0.5,0.75,1 --swaps-ratio=0,0.001,0.01,0.05,0.1,0.5 --reverse=true 100"            |>.splitOn " "
