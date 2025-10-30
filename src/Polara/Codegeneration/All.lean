import Polara.Codegeneration.Utils
import Polara.Codegeneration.Parse
import Polara.Codegeneration.Jax.All
import Polara.Codegeneration.Lean.All
import Polara.Codegeneration.Python.All
import Polara.Codegeneration.IO.All
---

def run (lang)[c: Codegen lang][ext: FileExt lang][b: BuildCode lang][e: ExeCode lang]
  (limit:= BenchRes.test){α: Ty}(term: Tm VPar α)(name: String) := do
      let code := c.gen term
      let file  ← writeCodeFile code lang s!"{name}"
      let _     ← b.bld file
      let (out, res) ← benchmarkIOM (e.exe file) limit
      let val  := α.parse out
      return (out, val, res)

abbrev Run := {α: Ty} → (term: Tm VPar α) → (name: String) → IO (String × α.val? × BenchRes)

def runners (limit := BenchRes.test): List (String × Run) := [
    ("Lean", run "Lean" limit),
    ("Python", run "Python" limit),
    -- ("Jax", run "Jax" limit)
  ]
