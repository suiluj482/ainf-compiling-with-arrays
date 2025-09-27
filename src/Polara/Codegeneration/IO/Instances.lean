import Polara.Codegeneration.IO.Utils
open System

--- lean ---
instance: FileExt "Lean" := ⟨"lean"⟩

instance leanBld: BuildCode "Lean" where
  bld (_) := pure ()

instance leanExe: ExeCode "Lean" where
  exe (path) := exeCom {
      cmd := "lean"
      args := #["--run", path.toString]
    }


--- python ---
instance: FileExt "Python" := ⟨"py"⟩

instance pythonBld: BuildCode "Python" where
  bld (_) := pure ()

instance pythonExe: ExeCode "Python" where
  exe (path) := exeCom {
    cmd := "python3"
    args := #[path.toString]
  }

--- jax ---
instance: FileExt "Jax" := ⟨"py"⟩
instance jaxBld: BuildCode "Jax" where
  bld := pythonBld.bld
instance jaxExe: ExeCode "Jax" where
  exe := pythonExe.exe
