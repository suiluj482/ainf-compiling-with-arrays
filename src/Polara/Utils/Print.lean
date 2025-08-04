def String.indent (s: String): String := "\n  " ++ s.replace "\n" "\n  "
def String.parens (s: String): String := s!"({s})"

def List.toStringSep [ToString α](sep: String): List α → String
  | [] => ""
  | [x] => toString x
  | x::xs => toString x ++ sep ++ xs.toStringSep sep

namespace Print

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

  def foldLine: List String → String := List.foldl (fun accu a => accu ++ " " ++ a ++ " |") "|"

  def printTableHeaderWithIndent (header: List String)(indent: Nat): IO Unit :=
    do
      printLineWithIndent (foldLine header) indent
      printLineWithIndent (foldLine <| header.map (fun _ => "---")) indent

  structure IoFoldPrecedingSeperatorFormat where
  begin: String
  sep: String
  ende: String

  def IoFoldPrecedingSeperatorFormatTableLine: IoFoldPrecedingSeperatorFormat := ⟨"| ", " | ", " |"⟩
  def IoFoldPrecedingSeperatorFormatLines (indent: Nat): IoFoldPrecedingSeperatorFormat := ⟨Print.indentString indent, "\n" ++ Print.indentString indent, "\n"⟩

end Print
