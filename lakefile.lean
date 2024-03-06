import Lake
open Lake DSL

package «quicksort» where
  -- -- Settings applied to both builds and interactive editing
  -- leanOptions := #[
  --   ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
  --   ⟨`pp.proofs.withType, false⟩
  -- ]
  -- add any additional package configuration options here
-- require std from git "https://github.com/leanprover/std4.git" @ "v4.6.1"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.6.1"
-- require supertype from git "https://github.com/somombo/supertype" @ "main"

@[default_target]
lean_lib «Quicksort» where
  -- add any library configuration options here

-- @[default_target]
lean_exe «quicksort» where
  root := `Example
