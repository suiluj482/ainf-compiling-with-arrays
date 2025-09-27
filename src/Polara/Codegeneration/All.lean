import Polara.Codegeneration.Utils
import Polara.Codegeneration.Parse
import Polara.Codegeneration.Jax.All
import Polara.Codegeneration.Lean.All
import Polara.Codegeneration.Python.All
import Polara.Codegeneration.IO.All
---

def runners: List (String × Run) := [

  ]

-- import Polara.Tests.Utils

-- def runners: List (String × (Tm VPar α → IO String)) := [
--   ("Lean", RunTmLean.run),
--   ⟨"Python", RunTmPy.run⟩,
--   ⟨"Jax", RunTmJax.run⟩
-- ]

-- def runner: Runner (Sigma (Tm VPar)) := λ ⟨α, tm⟩ => do
--   let results ← runners.mapM (λ (name, run) => do
--     let res ← run tm
--     return (name, res)
--   )
--   return (
--     "\n" ++ (results.map (λ (n, res) => s!"{n}: {res}") |>.foldl (λ acc x => s!"{acc}  | {x}") "" |>.dropRight 1),
--     α.allOkAndSimilar (results.map Prod.snd)
--   )
