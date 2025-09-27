import Polara.Codegeneration.IO.Config
import Polara.Codegeneration.IO.Classes

import Lean
open System

def readFile (filename : FilePath) : IO String := do
  let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
  let contents ← handle.readToEnd
  return contents

def copyInRuntime (code: String)
  (lang: String)[i: FileExt lang] : IO String := do
    let runtime ← readFile (getRuntimePath lang i.ext)
    return s!"{runtime}\n{code}"

def getTmpPath (file: String): FilePath := tmpDir.addExtension file
def writeTmpFile(file: String)(content: String): IO FilePath := do
  let path := getTmpPath file
  IO.FS.writeFile path content
  return path

def writeCodeFile (code: String)
  (lang: String)[i: FileExt lang]
  (file: String): IO FilePath := do
    let content ← copyInRuntime code lang
    writeTmpFile file content

def exeCom (args: IO.Process.SpawnArgs): IO String := do
  let output ← IO.Process.output args
  return if output.exitCode == 0
    then output.stdout
    else s!"{output.stdout}\nstderr{output.stderr}"
