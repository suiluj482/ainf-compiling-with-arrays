import Lean
import Polara.Syntax.Definitions
-- import Polara.Codegeneration.All

-- tothink
-- - reinkopierne vs importieren
-- - save (tmp) file?

--------------------------------------------------------------
-- Basics
--------------------------------------------------------------

class FileExt (name: String) where
  ext: String -- fileExtension

instance : FileExt "Lean" := ⟨"lean"⟩
instance : FileExt "Python" := ⟨"py"⟩
instance : FileExt "Jax" := ⟨"py"⟩

--------------------------------------------------------------
-- Runtime Handling
--------------------------------------------------------------

def directoryTmp: String := "Polara/.tmp/"
def writeFile(filename : String) (content : String) : IO Unit := do
  IO.FS.writeFile (directoryTmp ++ filename) content

def readFile (filename : String) : IO String := do
  let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
  let contents ← handle.readToEnd
  return contents
def copyInFile(script: String)(path: String) : IO String := do
  let content ← readFile path
  pure <| content ++ "\n" ++ script

def getRuntimePath(name: String)[r: FileExt name] :=
  s!"Polara/Codegeneration/{name}/Runtime.{r.ext}"
def Runtime.read(name: String)[FileExt name] : IO String :=
  readFile (getRuntimePath name)

def copyInRuntime (name: String)[FileExt name](script: String) : IO String :=
  copyInFile script (getRuntimePath name)

-- Alternative approach importing
class RuntimeImport (name: String) where
  importStatement: String

instance: RuntimeImport "Lean" :=
  ⟨"import Polara.Codegeneration.Lean.Runtime"⟩

def pythonImport (name: String): RuntimeImport name :=
  ⟨s!"import sys
sys.path.append(\"../Codegeneration\")
from {name}.Runtime import *
"⟩
instance: RuntimeImport "Python" := pythonImport "Python"
instance: RuntimeImport "Jax" := pythonImport "Jax"

-----------------------------------------------------------
-- Run Code
-----------------------------------------------------------
class RunScript (name: String) where
  run (script: String): IO String

-- special case includes print
def runLean (e : String) : IO String := do
  Lean.initSearchPath (← Lean.findSysroot)
  let r ← IO.mkRef {}
  let s := IO.FS.Stream.ofBuffer r
  let s' : IO.FS.Stream ← IO.setStdout s
  let prog := s!"
import Polara.Codegeneration.Lean.Runtime
#eval do
  IO.println ({e})
  IO.println \"§\" "
  -- IO.println prog
  let _ ← Lean.Elab.runFrontend prog {} "" .anonymous
  let _ ← IO.setStdout s'
  return ((String.join <| (← r.get).data.toList.map
    (String.singleton ∘ Char.ofNat ∘ Fin.val ∘ UInt8.toFin)).splitOn ("§\n")).head!.dropRight 2
instance : RunScript "Lean" := ⟨runLean⟩

def runPythonScript (script: String) : IO String := do -- IO (Except String String)
  let output ← IO.Process.output {
    cmd := "python3"
    args := #["-c", script]
  }
  pure <|
    if output.exitCode == 0 then
      "ok: " ++ output.stdout
    else
      output.stderr
instance : RunScript "Python" := ⟨runPythonScript⟩
instance : RunScript "Jax" := ⟨runPythonScript⟩

-- alternative: run from file
class RunFile (name: String) where
  run (file: String): IO String

def runPythonFile (path: String) : IO String := do -- IO (Except String String)
  let output ← IO.Process.output {
    cmd := "python3"
    args := #[path]
  }
  pure <|
    if output.exitCode == 0 then
      output.stdout
    else
      output.stderr
instance : RunFile "Python" := ⟨runPythonFile⟩
instance : RunFile "Jax" := ⟨runPythonFile⟩

---------------------------------------------------------------
-- Run
---------------------------------------------------------------

def runWithRuntime (name: String)[FileExt name][r: RunScript name] (e : String) : IO String := do
  r.run (← copyInRuntime name e)



-- -- def kontinuationLean(args: List String): String → String :=
-- --   (s!"  match {·}{args.foldl (s!"{·} {·}") ""} with
-- --   | .ok x => toString x
-- --   | .error e => \"error: \" ++ e"
-- --   )
-- def kontinuationLean(args: List String): String → String :=
--   (s!"  {·}{args.foldl (s!"{·} {·}") ""}")
-- def kontinuationPython(args: List String): String → String :=
--   (s!"print({·}({args.foldl (s!"{·}, {·}") "" |>.drop 2}), end='')")


-- def doAll(name: String)(tm: Tm VPar α)(args: List String) : IO String := do
--   writeFile s!"{name}.polara" tm.toString
--   let ainfUnoptimized := tm.toAINF
--   writeFile s!"{name}_unoptimized.ainf" ainfUnoptimized.toString
--   let ainf := ainfUnoptimized.cse
--   writeFile s!"{name}.ainf" ainf.toString

--   let doLean: IO String := do
--     let script := ainf.codegen <| kontinuationLean args
--     let script' := s!"
-- import Polara.Codegeneration.Lean.Runtime

-- #eval do
--   IO.println ({script.indent}
--   )
--   IO.println \"§\" "
--     let eval ← runLean script
--     writeFile s!"{name}.lean" script'
--     pure eval

--   let doPython: IO String := do
--     let script := ainf.codegenPy <| kontinuationPython args
--     let script' := (pythonImport "Python") ++ script
--     -- writeFile s!"{name}.py" script'
--     -- let eval ← runPythonFile (directoryTmp ++ s!"{name}.py")
--     -- let script' ← tuple (copyInRuntime script) pythonConfig
--     let eval ← runPythonScript script'
--     writeFile s!"{name}.py" (pythonImportForFile ++ script')
--     pure eval

--   let doPythonJax: IO String := do
--     let script := ainf.codegenJax <| kontinuationPython args
--     let script' := (pythonImport "PythonJax") ++ script
--     -- writeFile s!"{name}_jax.py" script'
--     -- let eval ← runPythonFile (directoryTmp ++ s!"{name}_jax.py")
--     -- let script' ← tuple (copyInRuntime script) pythonJaxConfig
--     let eval ← runPythonScript script'
--     writeFile s!"{name}_jax.py" (pythonImportForFile ++ script')
--     pure eval

--   let evals: List String := [
--     ← doLean,
--     ← doPython,
--     ← doPythonJax
--   ]

--   pure evals.toString
