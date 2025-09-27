import Lean
open System

def tmpDir: FilePath := "Polara/.tmp/"
def getRuntimePath(lang: String)(ext: String): FilePath :=
  s!"Polara/Codegeneration/{lang}/Runtime.{ext}"
