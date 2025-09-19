import Polara.Codegeneration.RunCode
import Polara.Codegeneration.Utils
import Polara.Codegeneration.Parse
import Polara.Codegeneration.Jax.All
import Polara.Codegeneration.Lean.All
import Polara.Codegeneration.Python.All
---

import Polara.Tests.Utils

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
  ⟨runWithRuntime "Python" ∘ (s!"print({Codegen.gen "Python" ·})")⟩
instance RunTmJax: RunTm "Jax" :=
  ⟨runWithRuntime "Jax" ∘ (s!"print(to_py({Codegen.gen "Jax" ·}))")⟩

def runners: List (String × (Tm VPar α → IO String)) := [
  ("Lean", RunTmLean.run),
  ⟨"Python", RunTmPy.run⟩,
  ⟨"Jax", RunTmJax.run⟩
]

def runner: Runner (Sigma (Tm VPar)) := λ ⟨α, tm⟩ => do
  let results ← runners.mapM (λ (name, run) => do
    let res ← run tm
    return (name, res)
  )
  return (
    "\n" ++ (results.map (λ (n, res) => s!"{n}: {res}") |>.foldl (λ acc x => s!"{acc}  | {x}") "" |>.dropRight 1),
    α.allOkAndSimilar (results.map Prod.snd)
  )
