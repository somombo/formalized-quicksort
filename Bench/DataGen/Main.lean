
import DataGen.Defaults
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

def «{» := "{"
def «}» := "}"

def make_input (sizes : List Nat) (params : List (Bool × Float × Float) := [(false, 1.0, 1.0)]) : IO Unit := do
  for size in sizes do
    if size = 0 then continue
    let outDir := System.FilePath.mk "data/input"
    let outFile := outDir / s!"{size}.csv"
    IO.FS.createDirAll outDir
    let handle ← IO.FS.Handle.mk outFile IO.FS.Mode.append

    for _' : i in List.range params.length do
      let (reverse, duplicate_ratio, swaps_ratio) := params[i]'(by grind)
      let data ← Array.randNats size (duplicate_ratio := duplicate_ratio) (swaps_ratio := swaps_ratio) (reverse := reverse)
      let data : String := data.extract 1 |>.foldl (· ++ "," ++ toString ·) s!"{data[0]!}"
      let current_time ← Std.Time.ZonedDateTime.now
      let current_time := current_time.format "uuuu-MM-dd'T'HH:mm:ssXXX"
      let datagen_method := s!"{i}#uniform_dist:{duplicate_ratio}:{swaps_ratio}:{reverse}:{size}"
      let id := hash data

      handle.putStrLn s!"{id},{current_time},{datagen_method},{data}"
      handle.flush -- TODO: somombo> is this necessary?
      println! s!"Generated array with {«{»}size := {size}, \
      duplicate_ratio := {duplicate_ratio}, swaps_ratio := {swaps_ratio}, \
      reverse := {reverse}{«}»}"
  println! s!"Added {sizes.length * params.length} arrays to the dataset"
open Cli

def main (args : List String) : IO UInt32 := Cmd.validate (args:=args)
$ (fun run => `[Cli|
  datagen VIA run;
  "The datagen command generates the arrays to be tested"
  FLAGS:
    u, "unique-ratio" : Array Float;      "--unique-ratio comma-separated floats. A list of unique-ratios"
    s, "swaps-ratio" : Array Float;       "--swaps-ratio comma-separated floats. A list of swaps-ratios"
    r, reverse;                     "--reverse description"
    f, forward;                     "--forward opposite of reverse"

  ARGS:
    ...sizes : Nat;                     "the array size"

  EXTENSIONS:
    defaultValues! #[("unique-ratio", "0"), ("swaps-ratio", "1")]
])
$ (fun p => do

  let sizes : Array Nat := p.variableArgsAs! Nat
  if sizes.size > 0 then

    let unique_ratios := p.flag! "unique-ratio" |>.as! (Array Float)
    let swaps_ratios := p.flag! "swaps-ratio" |>.as! (Array Float)
    -- let reverses := p.flag! "reverse" |>.as! (Array Bool)
    -- let reverse := p.flag? "reverse" |>.isSome

    let reverses :=
      match (p.flag? "reverse", p.flag? "forward") with
      | ⟨some _, some _⟩ => [true,false]
      | ⟨some _, none⟩ => [true]
      | ⟨none, _⟩ => [false]

    let _ ← make_input (sizes.toList) (reverses ×' swaps_ratios.toList ×' unique_ratios.toList)
    return 0
  else
    let _ ← make_input SIZES GENERAL_PARAMS
    println! s!"Warn: The `sizes` arguments have not been provided. Ignored all flags and run with defaults instead. See DataGen/Defaults.lean"
    return 0
)
