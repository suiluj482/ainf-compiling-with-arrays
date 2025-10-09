import Polara.Codegeneration.Utils
import Polara.Codegeneration.Parse
import Polara.Codegeneration.Jax.All
import Polara.Codegeneration.Lean.All
import Polara.Codegeneration.Python.All
import Polara.Codegeneration.IO.All
---

def run (lang)[c: Codegen lang][ext: FileExt lang][b: BuildCode lang][e: ExeCode lang]
  {α: Ty}(term: Tm VPar α)(name: String) := do
      let code := c.gen term
      let file  ← writeCodeFile code lang s!"{name}"
      let _     ← b.bld file
      let (out, time) ← benchmarkIO (e.exe file)
      let val  := α.parse out
      return (out, val, time)

abbrev Run := {α: Ty} → (term: Tm VPar α) → (name: String) → IO (String × α.val? × Float)


abbrev BenchRes := Nat × Float -- iterations, time

def runners: List (String × Run) := [
    ("Lean", run "Lean"),
    ("Python", run "Python"),
    -- ("Jax", run "Jax")
  ]
