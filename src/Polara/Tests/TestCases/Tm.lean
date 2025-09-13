import Polara.Codegeneration.All
import Polara.Tests.Utils

def runners: List (String × (AINF α → IO String)) := [
  ("Lean", RunAINFLean.run),
  ("Py", RunAINFPy.run),
  ("Jax", RunAINFJax.run),
]
