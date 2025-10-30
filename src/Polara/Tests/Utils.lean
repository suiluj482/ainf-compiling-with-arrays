import Polara.Codegeneration.All
import Polara.Optimizations.All
import Polara.AD.All
import Polara.Tests.Examples.All

open Tree Ty

-- only first part gets optimized,
--   second part allows for example to apply functions to check them
--   third part is the expected value (if given)
abbrev TmTest := ((α β: Ty) × Tm VPar α × (Tm VPar α → Tm VPar β) × β.val?)
abbrev TmTestCase := TestCase TmTest
abbrev TmTree := Tree String TmTestCase

namespace TmTest

  def run (limit: BenchRes)(fullName: String)(tc: TmTestCase): IO Result := do
    let ⟨name, α, β, tm, f, expected⟩ := tc
    let fullName := s!"{fullName}/{name}"

    -- run for pipelines and langs
    let res: List (Tree String (String × String × β.val? × BenchRes)) ←
      (pipelines α).mapM (λ (name, pipeline) => do
        let fullName := s!"{fullName}/{name}"
        let _ ← writeTmpFile s!"{fullName}.polara" tm.toString

        let (optimizedTm, pipeMeta) ← pipeline.runMeta fullName tm
        let fullTm: Tm VPar _ := f optimizedTm

        let res ← (runners limit).mapM (λ ((name, run): String × Run) => do
            let fullName := s!"{name}_{fullName}"
            let (mes, val, benchRes) ← run fullTm fullName
            return Tree.leaf (name, mes, val, benchRes)
          )

        return Tree.node s!"{name}({pipeMeta})" res
      )
    let tree := Tree.node name res

    -- check vals
    let (flat, errors) := tree.flatten.seperateWith (λ (names, (name, mes, val, _)) =>
        let name := names.cons name |>.foldl (s!"{·}_{·}") ""
        match val with
        | some val => .inl (name, val, mes)
        | none => .inr s!"{fullName}{name}: no value: {mes}"
      )
    let errors := errors ++ match expected with
      | some expected =>
        flat.filterMap (λ (name, val, mes) =>
            if β.similarVal expected val
              then none
              else some s!"{fullName}{name}: expected: {expected}, got: {mes}"
          )
      | none =>
        flat.slidingPair.filterMap (λ ((n1, v1, m1), (n2, v2, m2)) =>
          if β.similarVal v1 v2
            then none
            else some s!"{fullName}{n1} and {n2} differ: got {m1} vs {m2}"
        )

    -- printable erg
    let tree' := tree.map id (λ (n,_,_,t) => s!"{n}|{t}")
    let text := tree'.prettyTable

    if errors.isEmpty then
      return (text, true)
    else
      return (s!"{Print.foldLines errors}\n{text}", false)


  def print (t: TmTree)(limit := BenchRes.test): IO Unit := do
    let name := (match t with
      | node name _ => name
      | leaf ⟨name,_⟩ => name)
    let res ← TestCaseTree.pretty ⟨_, t, run limit⟩
    let _ ← writeTmpFile s!"{name}/result.txt" res
    IO.println res

end TmTest
