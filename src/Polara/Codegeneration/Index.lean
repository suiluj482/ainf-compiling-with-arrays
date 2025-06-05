import Polara.Codegeneration.Lean.Index
import Polara.Codegeneration.Python.Index
import Polara.Codegeneration.Jax.Index

import Polara.Codegeneration.Utils
import Polara.Codegeneration.RunCode

class Codegen (name: String) where
  gen : Tm VPar α → String

class RunTm (name: String) where
  run: Tm VPar α → IO String

instance: Codegen "Lean" := ⟨Tm.codegen⟩
instance: Codegen "Python" := ⟨Tm.codegenPy⟩
instance: Codegen "Jax" := ⟨Tm.codegenJax⟩

instance RunTmLean: RunTm "Lean" :=
  ⟨RunScript.run "Lean" ∘ (Codegen.gen "Lean")⟩
instance RunTmPy: RunTm "Python" :=
  ⟨runWithRuntime "Python" ∘ (s!"print({Codegen.gen "Python" ·}")⟩
instance RunTmJax: RunTm "Jax" :=
  ⟨runWithRuntime "Jax" ∘ (s!"print({Codegen.gen "Jax" ·})")⟩
