import Polara.Codegeneration.Index
import Polara.Tests.TestCases


open TestCases

def runners: List (String × (AINF α → IO String)) := [
  ("Lean", RunAINFLean.run),
  ("Py", RunAINFPy.run),
  ("Jax", RunAINFJax.run),
]

def runTestCases : IO Unit := do
  testCases.map (λ ⟨name, _α, a⟩ => do
    IO.println s!"Test case: {name}"
    let results := runners.map (λ (n, run) => do
      IO.println s!"  {n}:"
      let res ← run a
      IO.println res
    )
    results.foldl (λ acc x => do acc; x) (pure ())
  )
  |>.foldl (λ acc x => do acc; x) (pure ())

-- #eval runTestCases

def runnersTm: List (String × (Term α → IO String)) := [
  -- ("Lean", runWithRuntime "Lean"   ∘ Tm.codegen),
  ("Py",   runWithRuntime "Python" ∘ (s!"print({·})") ∘ Tm.codegenPy),
  ("Jax",  runWithRuntime "Jax"    ∘ (s!"print({·})") ∘ Tm.codegenJax),
]
def runTestCasesTm : IO Unit := do
  testCases.map (λ ⟨name, α, a⟩ => do
    let tm: Term α := a.toTm
    IO.println s!"Test case: {name}"
    let results := runnersTm.map (λ (n, run) => do
      IO.println s!"  {n}:"
      let res ← run tm
      IO.println res
    )
    results.foldl (λ acc x => do acc; x) (pure ())
  )
  |>.foldl (λ acc x => do acc; x) (pure ())

-- #eval runTestCasesTm
