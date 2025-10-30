import Polara.Utils.Tree
import Polara.Utils.Functions

structure TestCase (α: Type u) where
  name: String
  val: α

def lookupTestCase (testCases: List (TestCase α)) (name: String): Option (TestCase α) :=
  testCases.find? (λ x => x.name == name)

-- running
def Result := String × Bool
def prettyOk: Bool → String
  | true => "pass"
  | false => "fail"
def prettyFail: Bool → String
  | true => ""
  | false => " fail"
def Runner (α) := String → TestCase α → IO Result

-- passed / total
def Score := Nat × Nat
def Score.zero: Score := (0, 0)
def Score.ofBool: Bool → Score := (if · then (1, 1) else (0, 1))
def Score.add (a b: Score) := (a.1 + b.1, a.2 + b.2)
def Score.perfect (s: Score) := s.1 == s.2
def Score.pretty (s: Score) := s!"{s.1} / {s.2} passed"

def TestCaseTree := (α: _) × Tree String (TestCase α) × Runner α

def TestCaseTree.run: TestCaseTree → IO (Tree (String × Score) Result)
| ⟨_, tree, run⟩ => do
  let tree := tree.mutPreorder
    (λ a fullName => (a, s!"{fullName}/{a}"))
    (λ v fullName => (fullName.drop 1, v)) ""
  let res ← (tree.map id (Func.tuple run)).leafM
  let (res, _) := res.mutPostorder
    (λ (_,ok) => Score.ofBool ok)
    (λ name scores =>
      let score := scores.foldl Score.add Score.zero
      ((name, score), score))
  return res

def TestCaseTree.pretty (tree: TestCaseTree): IO String :=
  return (← tree.run).map
    (λ (name, score) => s!"{name}{if score.perfect then "" else " "++score.pretty}")
    (λ (mes, ok) => if ok
      then mes
      else s!"{prettyOk ok}:\n{mes.indent}")
  |>.json

-- def TestCaseTree.pretty (tree: TestCaseTree): IO String :=
--   return (← tree.run).map
--     (λ (name, score) => s!"{name} {score.pretty}")
--     (λ (mes, ok) => s!"{prettyOk ok}:\n{mes.indent}")
--   |>.pretty

def TestCaseTree.print (tree: TestCaseTree): IO Unit := do
  IO.println (← tree.pretty)
