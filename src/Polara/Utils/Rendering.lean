import Polara.Utils.ListMap
import Polara.Utils.Print

private def colors := #["#ff5500", "#00aa00", "#ff00aa", "#555500",
 "#ffaa55", "#00ffff", "#ff55ff", "#55ffaa", "#ffaa00"]

private def modArrayAccess(arr: Array α)(ok: arr.size > 0)(n: Nat): α :=
  let i := n % arr.size
  have: i<arr.size := Nat.mod_lt n ok
  arr[i]

def color (n: Nat) := modArrayAccess colors (by simp[colors]) n

def htmlColorTag (n:Nat): String → String :=
  (s!"<font color=\"{color n}\">{·}</font>")

#eval htmlColorTag 0 "a"

def DListMap.toGraphviz (m: DListMap α β)(keys: ((γ:α)× β γ) → List α)(keyToString: α → String)(valueToString: ((γ:α)× β γ) → String): String :=
  let content := (m.map (λ ⟨k, v⟩ =>
      let kS := keyToString k
      let vS := valueToString ⟨k,v⟩
      let ksS := keys ⟨k,v⟩ |>.map keyToString |> Print.foldWithComma
      s!"{kS} [label=<{vS}>];\n"++
      s!"{ksS} -> {kS}"
    )
    |> Print.foldLines)
  "digraph G{\n  node [shape=box];\n"++content.indent++"\n}"

structure GraphvizNode where
  key: String
  keys: List String
  label: String

def GraphvizNodes.toGraphviz (l: List GraphvizNode): String :=
  let content := (l.map (λ n =>
      s!"{n.key} [label=<{n.label}>];\n"++
      if n.keys.length > 0 then s!"\{{n.keys |> Print.foldWithComma}} -> {n.key}" else ""
    )
    |> Print.foldLines)
  "digraph G{\n  node [shape=box];\n"++content.indent++"\n}"
