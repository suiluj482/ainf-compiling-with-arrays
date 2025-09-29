import Polara.Codegeneration.All
import Polara.Optimizations.All
import Polara.AD.All

open Tree Ty

namespace TmTest
  -- only first part gets optimized,
  --   second part allows for example to apply functions to check them
  --   third part is the expected value (if given)
  abbrev TmTest := ((α β: Ty) × Tm VPar α × (Tm VPar α → Tm VPar β) × β.val?)
  abbrev TmTestCase := TestCase TmTest
  abbrev TmTree := Tree String TmTestCase

  def tmTree: TmTree :=
    node "TmTestCases" [
      node "Primitives" [
        -- cst0
        leaf ⟨"litn", _,_,
          tlitn 42, id,
          some 42
        ⟩,
        leaf ⟨"litf", _,_,
          tlitf 3.14, id,
          some 3.14
        ⟩,
        leaf ⟨"liti", _,_,
          tliti (2: Fin 6), id,
          some 2
        ⟩,
        -- cst1
        leaf ⟨"exp",  _,_,    (tlitf 4.2).exp, id, none⟩,
        leaf ⟨"sqrt", _,_,    (tlitf 4.2).sqrt, id, none⟩,
        leaf ⟨"log",  _,_,    (tlitf 4.2).log, id, none⟩,
        leaf ⟨"normCdf", _,_, (tlitf 4.2).normCdf, id, none⟩,
        leaf ⟨"fst", _,_,    ((tlitf 4.2),, (tlitf 3.14)).fst, id, none⟩,
        leaf ⟨"snd", _,_,    ((tlitf 4.2),, (tlitf 3.14)).snd, id, none⟩,
        leaf ⟨"sum", _,_,    (for'v _:10 => tlitf 4.2).sumf, id, none⟩,
        leaf ⟨"i2n", _,_,    (tliti (2: Fin 6)).i2n, id, none⟩,
        leaf ⟨"n2f", _,_,    (tlitn 42).n2f, id, none⟩,
        -- cst2
        leaf ⟨"addn", _,_,  (tlitn 42) + (tlitn 2), id, none⟩,
        leaf ⟨"subn", _,_,  (tlitn 42) - (tlitn 2), id, none⟩,
        leaf ⟨"muln", _,_,  (tlitn 42) * (tlitn 2), id, none⟩,
        leaf ⟨"divn", _,_,  (tlitn 42) / (tlitn 2), id, none⟩,
        leaf ⟨"addf", _,_,  (tlitf 42.0) + (tlitf 2.0), id, none⟩,
        leaf ⟨"subf", _,_,  (tlitf 42.0) - (tlitf 2.0), id, none⟩,
        leaf ⟨"mulf", _,_,  (tlitf 42.0) * (tlitf 2.0), id, none⟩,
        leaf ⟨"divf", _,_,  (tlitf 42.0) / (tlitf 2.0), id, none⟩,
        leaf ⟨"adda", _,_,  (for'v _:10 => tlitf 4.2) + (for'v _:10 => tlitf 2.0), id, none⟩,
        leaf ⟨"suba", _,_,  (for'v _:10 => tlitf 4.2) - (for'v _:10 => tlitf 2.0), id, none⟩,
        leaf ⟨"mula", _,_,  (for'v _:10 => tlitf 4.2) * (for'v _:10 => tlitf 2.0), id, none⟩,
        leaf ⟨"diva", _,_,  (for'v _:10 => tlitf 4.2) / (for'v _:10 => tlitf 2.0), id, none⟩,
        leaf ⟨"addi", _,_,  (tliti (2: Fin 8)).addi (tliti (3: Fin 4)), id, none⟩,
        leaf ⟨"eqi",  _,_,  (tliti (2: Fin 3)).eqi (tliti (2: Fin 3)), id, none⟩,
        leaf ⟨"maxf", _,_,  (tlitf 42.0).maxf (tlitf 2.0), id, none⟩,
        leaf ⟨"lt", _,_,    (tlitf 42.0) <' (tlitf 2.0), id, none⟩,
        leaf ⟨"get", _,_,   (for'v _:10 => tlitf 4.2)[[(tliti (2: Fin 11))]], id, none⟩,
        leaf ⟨"tup", _,_,   ((tlitf 4.2),, (tlitn 42)), id, none⟩,
        leaf ⟨"app", _,_,   (fun'v _:nat => tlitf 4.2) @@ (tlitn 42), id, none⟩,
        -- tm
        leaf ⟨"var", _,_,   let' v := tlitf 4.2; v, id, none⟩,
        leaf ⟨"abs", _,_,   (fun'v _:nat => tlitf 4.2), (·@@ (tlitn 42)), none⟩,
        leaf ⟨"bld", _,_,   for'v _:10 => tlitf 4.2, id, none⟩,
        leaf ⟨"iteT", _,_,  if' (tlitn 1) then (tlitf 4.2) else (tlitf 2.4), id, none⟩,
        leaf ⟨"iteF", _,_,  if' (tlitn 0) then (tlitf 4.2) else (tlitf 2.4), id, none⟩,
      ],
      node "Simple" [
        leaf ⟨"vectorRange", _,_, (for' i:10 => i.i2n.n2f), id, none⟩,
      ],
      node "AD" [
        node "dualNumbers" [
          -- literals
          leaf ⟨"litnat", _,_,
            (tlitn 42).aD, id,
            some 42
          ⟩,
          leaf ⟨"litflt", _,_,
            (tlitf 3.14).aD, id,
            some (3.14, 0)
          ⟩,
          -- func
          leaf ⟨"id", _,_,
            (fun' x:flt => x).aD, (·@@ (tlitf 3.14,, tlitl 1.0)),
            some (3.14, 1.0)
          ⟩,
          -- cst1
          leaf ⟨"exp", _,_,
            (fun' x:flt => x.exp).aD, (·@@ (tlitf 0.0,, tlitl 1.0)),
            some (1.0, 1.0)
          ⟩,
          leaf ⟨"log", _,_,
            (fun' x:flt => x.log).aD, (·@@ (tlitf 1.0,, tlitl 1.0)),
            some (0.0, 1.0)
          ⟩,
          leaf ⟨"sqrt", _,_,
            (fun' x:flt => x.sqrt).aD, (·@@ (tlitf 4.0,, tlitl 1.0)),
            some (2.0, 0.25)
          ⟩,
          leaf ⟨"normCdf", _,_,
            (fun' x:flt => x.normCdf).aD, (·@@ (tlitf 0.0,, tlitl 1.0)),
            some (0.5, 0.3989422804)
          ⟩,
          leaf ⟨"fst", _,_,
            (fun' x:(flt ×× flt) => x.fst).aD,
            (·@@ ((tlitf 4.2,, tlitl 0.0),, (tlitf 3.14,, tlitl 1.0))),
            some (4.2, 0.0)
          ⟩,
          leaf ⟨"snd", _,_,
            (fun' x:(flt ×× flt) => x.snd).aD,
            (·@@ ((tlitf 4.2,, tlitl 0.0),, (tlitf 3.14,, tlitl 1.0))),
            some (3.14, 1.0)
          ⟩,
          leaf ⟨"sumf", _,_,
            (fun' x:(array 10 flt) => x.sumf).aD,
            (·@@ (for' i:10 => (tlitf 4.2,, tlitl 1.0))),
            some (42.0, 10.0)
          ⟩,
          leaf ⟨"n2f", _,_,
            (fun' x:nat => x.n2f).aD,
            (·@@ (tlitn 42)),
            some (42.0, 0.0)
          ⟩,
          -- cst2
          leaf ⟨"add", _,_,
            (fun' x:flt => fun' y:flt => x + y).aD,
            (·@@ (tlitf 40.0,, tlitl 1.0) @@ (tlitf 2.0,, tlitl 2.0)),
            some (42.0, 3.0)
          ⟩,
          leaf ⟨"sub", _,_,
            (fun' x:flt => fun' y:flt => x - y).aD,
            (·@@ (tlitf 44.0,, tlitl 1.0) @@ (tlitf 2.0,, tlitl 2.0)),
            some (42.0, -1.0)
          ⟩,
          leaf ⟨"mul", _,_,
            (fun' x:flt => fun' y:flt => x * y).aD,
            (·@@ (tlitf 21.0,, tlitl 1.0) @@ (tlitf 2.0,, tlitl 2.0)),
            some (42.0, 44.0)
          ⟩,
          leaf ⟨"div", _,_,
            (fun' x:flt => fun' y:flt => x / y).aD,
            (·@@ (tlitf 84.0,, tlitl 1.0) @@ (tlitf 2.0,, tlitl 2.0)),
            some (42.0, -41.5)
          ⟩,
          leaf ⟨"adda", _,_,
            (fun' x:(array 10 flt) => fun' y:(array 10 flt) => x + y).aD,
            (·@@ (for' i:10 => (tlitf 40.0,, tlitl 1.0)) @@ (for' i:10 => (tlitf 2.0,, tlitl 2.0))),
            some (Vector.replicate 10 (42.0, 3.0))
          ⟩,
          leaf ⟨"maxf", _,_,
            (fun' x:flt => fun' y:flt => x.maxf y).aD,
            (·@@ (tlitf 40.0,, tlitl 1.0) @@ (tlitf 42.0,, tlitl 2.0)),
            some (42.0, 2.0)
          ⟩,
          -- higher order functions
          leaf ⟨"curried", _,_,
            (fun' x:flt => fun' y:flt => x + y).aD,
            (·@@ (tlitf 4.0,, tlitl 1.0) @@ (tlitf 2.0,, tlitl 0.0)),
            some (6.0, 1.0)
          ⟩,
          leaf ⟨"curried2", _,_,
            (fun' x:flt => fun' y:flt => fun' z:flt => x + y).aD,
            (·@@ (tlitf 4.0,, tlitl 1.0) @@ (tlitf 2.0,, tlitl 0.0) @@ (tlitf 100.0,, tlitl 0.0)),
            some (6.0, 1.0)
          ⟩,
          leaf ⟨"higherorder", _,_,
            (fun' f:(flt ~> flt) => fun' x:flt => (tlitf 1.0) + (f @@ x)).aD,
            (·@@ (fun' y:flt××lin => (y.fst + (tlitf 1.0),, y.snd)) -- (·+1)
              @@ (tlitf 3.0,, tlitl 1.0)),
            some (5.0, 1.0)
          ⟩,
        ],
        node "df" [

        ],
        node "dr" [

        ],
      ],
    ]

  def TmTestCase.run (fullName: String)(tc: TmTestCase): IO Result := do
    let ⟨name, _, α, tm, f, expected⟩ := tc
    let fullName := s!"{fullName}/{name}"

    -- run for pipelines and langs
    let res ← pipelines.mapM (λ (name, pipeline) => do
      let fullName := s!"{fullName}/{name}"
      let (optimizedTm, time) ← benchmarkIOF tm (pipeline fullName)
      let fullTm := f optimizedTm

      let _ ← writeTmpFile s!"{fullName}.polara" optimizedTm.toString

      let res ← runners.mapM (λ (name, run) => do
          let fullName := s!"{fullName}_{name}"
          let (mes, val, time) ← run fullTm fullName
          return Tree.leaf (name, mes, val, time)
        )

      return Tree.node s!"{name}({time})" res
    )
    let tree := Tree.node name res

    -- check vals
    let (flat, errors) := tree.flatten.seperateWith (λ (names, (name, mes, val, _)) =>
        let name := names.cons name |>.foldl (s!"{·}_{·}") ""
        match val with
        | some val => .inl (name, val, mes)
        | none => .inr s!"{fullName}{name}: no value {mes}"
      )
    let errors := errors ++ match expected with
      | some expected =>
        flat.filterMap (λ (name, val, mes) =>
            if α.similarVal expected val
              then none
              else some s!"{fullName}{name}: expected {expected}, got {mes}"
          )
      | none =>
        flat.slidingPair.filterMap (λ ((n1, v1, m1), (n2, v2, m2)) =>
          if α.similarVal v1 v2
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


  def print: IO Unit := do
    let res ← TestCaseTree.pretty ⟨_, tmTree, TmTestCase.run⟩
    let _ ← writeTmpFile "TmTestCases/result.txt" res
    IO.println res

end TmTest
