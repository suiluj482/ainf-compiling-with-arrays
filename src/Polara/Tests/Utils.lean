import Polara.Utils.Index

structure TestCase (α: Type u) where
  name: String
  val: α

def lookupTestCase (testCases: List (TestCase α)) (name: String): Option (TestCase α) :=
  testCases.find? (λ x => x.name == name)

def Runner (α) := α → IO (String × Bool)

-- passed / total
def Score := Nat × Nat
def Score.add (a b: Score) := (a.1 + b.1, a.2 + b.2)
def Score.pretty (s: Score) := s!"{s.1} / {s.2} passed"

-- todo header zeile?
def TestCaseGroup := String × (α: _) × List (TestCase α) × Runner α
def TestCaseResults := String × List (String × Bool) × Score
def runTestCaseGroup: TestCaseGroup → IO TestCaseResults
  | ⟨name, _, testCases, runner⟩ => do
    let res ← testCases.mapM (λ t => do return (← runner t.val).map (s!"{t.name}: {·}") id)
    return (name, res, (res.filter (λ (_, ok) => ok) |>.length, res.length))

def TestCaseTree := Tree String TestCaseGroup

def TestCaseTree.run (tree: TestCaseTree): IO (Tree (String × Score) (TestCaseResults)) := do
  let res ← tree.map id runTestCaseGroup |>.leafM
  let rec tmp: Tree String TestCaseResults → (Tree (String × Score) TestCaseResults) × Score := λ
  | Tree.leaf (name, res, score) => (Tree.leaf (name, (res), score), score)
  | Tree.node name ts =>
    let ts' := ts.map tmp
    let scores := ts'.map Prod.snd |>.foldr Score.add (0, 0)
    (Tree.node (name, scores) (ts'.map Prod.fst), scores)
  return (tmp res).fst

def TestCaseTree.pretty (tree: TestCaseTree): IO String := do return (
  (← tree.run).map
    (λ (name, score) => s!"{name} {score.pretty}")
    (λ (name, res, score) =>
      let res' := res.map
        (λ ((s, ok): String × Bool) => s!"{ok} | {s}")
        |>.foldr (s!"{·}\n{·}") ""
      s!"{name} {score.pretty}: ({res'.indent.dropRight 2})")
  |>.pretty
)

def TestCaseTree.print (tree: TestCaseTree): IO Unit := do
  IO.println (← tree.pretty)
