import Lean
open System

def readFile (filename : FilePath) : IO String := do
  let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
  let contents ← handle.readToEnd
  return contents

namespace String
  def addToLines (s: String)(pre: String): String := pre ++ s.replace "\n" s!"\n{pre}"
  def indent (s: String): String := addToLines s "  "
  def parens (s: String): String := s!"({s})"
  def ensurePrefix (s: String)(pre: String): String :=
    if s.startsWith pre then s else pre ++ s
  def ensureLineBreak (s: String): String :=
    s.ensurePrefix "\n"
end String

def List.toStringSep [ToString α](sep: String): List α → String
  | [] => ""
  | [x] => toString x
  | x::xs => toString x ++ sep ++ xs.toStringSep sep

namespace Print

  def foldLines: List String → String | l => l.foldl (s!"{·}\n{·}") "" |>.drop 1

  def foldWithComma: List String → String | l => l.foldl (s!"{·},{·}") "" |>.drop 1

  def indentString (n: Nat): String :=
    match n with
    | 0 => ""
    | n+1 => indentString n ++ "  "

  def printLineWithIndent (line: String)(indent: Nat): IO Unit :=
    IO.println <| (indentString indent) ++ line

  def printLinesWithIndent (list: List String)(indent: Nat): IO Unit :=
    list.foldl (fun (acc: IO Unit) (x: String) =>
          do
            acc
            printLineWithIndent x indent
        ) (IO.print "")

  def foldTableLine: List String → String := List.foldl (fun accu a => accu ++ " " ++ a ++ " |") "|"


  def printTableHeaderWithIndent (header: List String)(indent: Nat): IO Unit :=
    do
      printLineWithIndent (foldTableLine header) indent
      printLineWithIndent (foldTableLine <| header.map (fun _ => "---")) indent

  structure IoFoldPrecedingSeperatorFormat where
  begin: String
  sep: String
  ende: String

  def IoFoldPrecedingSeperatorFormatTableLine: IoFoldPrecedingSeperatorFormat := ⟨"| ", " | ", " |"⟩
  def IoFoldPrecedingSeperatorFormatLines (indent: Nat): IoFoldPrecedingSeperatorFormat := ⟨Print.indentString indent, "\n" ++ Print.indentString indent, "\n"⟩

end Print
