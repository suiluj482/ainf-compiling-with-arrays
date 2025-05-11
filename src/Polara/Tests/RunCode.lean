import Lean

def readFile (filename : String) : IO String := do
  let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
  let contents ← handle.readToEnd
  return contents

-- über files? where?

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
  let _ ← Lean.Elab.runFrontend prog {} "" .anonymous
  let _ ← IO.setStdout s'
  return ((String.join <| (← r.get).data.toList.map
    (String.singleton ∘ Char.ofNat ∘ Fin.val ∘ UInt8.val)).splitOn ("§\n")).head!.dropRight 2

#eval runLean "1+1"

def runPython (script: String) : IO String := do -- IO (Except String String)
  let runtime ← readFile "Polara/Codegeneration/Python/Runtime.py"
  let programm := runtime ++ "\n" ++ script

  let output ← IO.Process.output {
    cmd := "python3"
    args := #["-c", programm]
  }
  pure <|
    if output.exitCode == 0 then
      output.stdout
    else
      output.stderr

#eval runPython "print('hi')"
