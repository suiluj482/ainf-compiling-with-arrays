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
    let _ ← writeTmpFile s!"{fullName}/_.polara" tm.toString

    -- run for pipelines and langs
    let res: List ((Tree String String) × (Tree String (String × String × β.val?))) ←
      (pipelines α).mapM (λ (name, pipeline) => do
        let fullName := s!"{fullName}/{name}"

        let pipeRes ← PipelineM.runMeta fullName tm pipeline
        let optimizedTm := pipeRes.fst; let pipeMeta := pipeRes.snd
        let fullTm: Tm VPar _ := f optimizedTm

        let runRes ← (runners limit).mapM (λ ((name, run): String × Run) => do
            let fullName := s!"{fullName}_{name}"
            let (mes, val, benchRes) ← run fullTm fullName
            return (name, mes, val, benchRes)
          )

        return (
          Tree.node name (
            (if pipeMeta.isEmpty then [] else
             [(Tree.node "pipelineSteps" pipeMeta).jsonArrayInline,])
          ++ [
           (Tree.node "runners" (runRes.map
              (λ (name, _mes, _val, benchRes) =>
                Tree.leaf s!"\"{name}\": {"{"} \"avTime\": {benchRes.avTime}, \"time\": {benchRes.time}, \"iterations\": {benchRes.it} {"}"}"
              )
            )).jsonArrayInline,
          ]),
          Tree.node name (runRes.map (λ (name, mes, val, _) => Tree.leaf (name, mes, val)))
        )
      )
    let (resInfo, resVals) := res.unzip
    let resTree := Tree.node name resInfo

    -- check vals
    let treeVals := Tree.node name resVals
    let (flat, errors) := treeVals.flatten.seperateWith (λ (names, (name, mes, val)) =>
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
    let text := resTree.json'

    if errors.isEmpty then
      return (text, true)
    else
      return (s!"{Print.foldLines errors}\n{text}", false)


  def print (t: TmTree)(limit := BenchRes.test): IO Unit := do
    let name := (match t with
      | node name _ => name
      | leaf ⟨name,_⟩ => name)
    let res ← TestCaseTree.pretty ⟨_, t, run limit⟩
    let _ ← writeTmpFile s!"{name}/result.json" res
    IO.println res

end TmTest
