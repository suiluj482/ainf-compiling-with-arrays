import Polara.Codegeneration.IO.Config
import Polara.Codegeneration.IO.Classes
import Polara.Utils.All

import Lean
open System

def copyInRuntime (code: String)
  (lang: String)[i: FileExt lang] : IO String := do
    let runtime ← readFile (getRuntimePath lang i.ext)
    return s!"{runtime}\n{code}"

def getTmpPath (file: String): FilePath := tmpDir.join file
def writeTmpFile(file: String)(content: String): IO FilePath := do
  let path := getTmpPath file
  match path.parent with
  | some parent => IO.FS.createDirAll parent
  | none        => pure ()
  IO.FS.writeFile path content
  return path

def writeCodeFile (code: String)
  (lang: String)[i: FileExt lang]
  (file: String): IO FilePath := do
    let content ← copyInRuntime code lang
    writeTmpFile s!"{file}.{i.ext}" content

def exeCom (args: IO.Process.SpawnArgs): IO String := do
  let output ← IO.Process.output args
  return match output.exitCode with
   | 0 => output.stdout
   | 124 => "timeout after 10s"
   | _ => s!"(stdout{output.stdout}\nstderr{output.stderr})"
