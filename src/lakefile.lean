import Lake
open Lake DSL

package «Polara» where
  leanOptions := #[
    ⟨`relaxedAutoImplicit, false⟩
  ]

lean_lib «Polara» where

@[default_target]
lean_exe «polara» where
  root := `Main

lean_exe «test» where
  root := `Polara.Test
  supportInterpreter := true
