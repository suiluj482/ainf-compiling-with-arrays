import Polara.Codegeneration.Lean.Index
import Polara.Codegeneration.Python.Index
import Polara.Codegeneration.Jax.Index

import Polara.Codegeneration.Utils
import Polara.Codegeneration.RunCode

class Codegen (name: String) where
  gen (k: String → String): AINF α → String

class RunAINF (name: String) where
  run: AINF α → IO String

instance: Codegen "Lean" := ⟨AINF.codegen⟩
instance: Codegen "Python" := ⟨AINF.codegenPy⟩
instance: Codegen "Jax" := ⟨AINF.codegenJax⟩

instance RunAINFLean: RunAINF "Lean" :=
  ⟨RunScript.run "Lean" ∘ (Codegen.gen "Lean" (s!"{·}"))⟩
instance RunAINFPy: RunAINF "Python" :=
  ⟨runWithRuntime "Python" ∘ (Codegen.gen "Python" (s!"print({·})"))⟩
instance RunAINFJax: RunAINF "Jax" :=
  ⟨runWithRuntime "Jax" ∘ (Codegen.gen "Jax" (s!"print({·})"))⟩
