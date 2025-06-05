import Lake
open Lake DSL

package «Polara» where
  leanOptions := #[
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

lean_lib «Polara» where

@[default_target]
lean_exe «polara» where
  root := `Main

lean_exe «test» where
  root := `Polara.Tests.Main
  supportInterpreter := true
