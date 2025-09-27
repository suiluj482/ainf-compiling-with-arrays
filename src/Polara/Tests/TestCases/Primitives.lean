import Polara.Codegeneration.All
import Polara.Tests.Utils

open Notations Ty Const0 Const1 ArithOp Const2 Prim AINF EnvPart

-- only first part gets optimized
abbrev TmTestCase := {α β: Ty} → Tm VPar α × (Tm VPar α → Tm VPar β)

def ainfSimpleTestCases : List (TestCase (Sigma (Tm VPar))) := [
  -- cst0
  ⟨"litn", _,  tlitn 42⟩,
  ⟨"litf", _,  tlitf 3.14⟩,
  ⟨"liti", _,  tliti (2: Fin 6)⟩,
  -- cst1
  ⟨"exp",  _,    (tlitf 4.2).exp⟩,
  ⟨"sqrt", _,    (tlitf 4.2).sqrt⟩,
  ⟨"log",  _,    (tlitf 4.2).log⟩,
  ⟨"normCdf", _, (tlitf 4.2).normCdf⟩,
  ⟨"fst", _,    ((tlitf 4.2),, (tlitf 3.14)).fst⟩,
  ⟨"snd", _,    ((tlitf 4.2),, (tlitf 3.14)).snd⟩,
  ⟨"sum", _,    (for'v _:10 => tlitf 4.2).sumf⟩,
  ⟨"i2n", _,    (tliti (2: Fin 6)).i2n⟩,
  ⟨"n2f", _,    (tlitn 42).n2f⟩,
  -- cst2
  ⟨"addn", _,  (tlitn 42) + (tlitn 2)⟩,
  ⟨"subn", _,  (tlitn 42) - (tlitn 2)⟩,
  ⟨"muln", _,  (tlitn 42) * (tlitn 2)⟩,
  ⟨"divn", _,  (tlitn 42) / (tlitn 2)⟩,
  ⟨"addf", _,  (tlitf 42.0) + (tlitf 2.0)⟩,
  ⟨"subf", _,  (tlitf 42.0) - (tlitf 2.0)⟩,
  ⟨"mulf", _,  (tlitf 42.0) * (tlitf 2.0)⟩,
  ⟨"divf", _,  (tlitf 42.0) / (tlitf 2.0)⟩,
  ⟨"adda", _,  (for'v _:10 => tlitf 4.2) + (for'v _:10 => tlitf 2.0)⟩,
  ⟨"suba", _,  (for'v _:10 => tlitf 4.2) - (for'v _:10 => tlitf 2.0)⟩,
  ⟨"mula", _,  (for'v _:10 => tlitf 4.2) * (for'v _:10 => tlitf 2.0)⟩,
  ⟨"diva", _,  (for'v _:10 => tlitf 4.2) / (for'v _:10 => tlitf 2.0)⟩,
  ⟨"addi", _,  (tliti (2: Fin 8)).addi (tliti (3: Fin 4))⟩,
  ⟨"eqi",  _,  (tliti (2: Fin 3)).eqi (tliti (2: Fin 3))⟩,
  ⟨"maxf", _,  (tlitf 42.0).maxf (tlitf 2.0)⟩,
  ⟨"lt", _,    (tlitf 42.0) <' (tlitf 2.0)⟩,
  ⟨"get", _,   (for'v _:10 => tlitf 4.2)[[(tliti (2: Fin 11))]]⟩,
  ⟨"tup", _,   ((tlitf 4.2),, (tlitn 42))⟩,
  ⟨"app", _,   (fun'v _:nat => tlitf 4.2) @@ (tlitn 42)⟩,
  -- tm
  ⟨"var", _,   let' v := tlitf 4.2; v⟩,
  ⟨"abs", _,   (fun'v _:nat => tlitf 4.2) @@ (tlitn 42)⟩,
  ⟨"bld", _,   for'v _:10 => tlitf 4.2⟩,
  ⟨"iteT", _,  if' (tlitn 1) then (tlitf 4.2) else (tlitf 2.4)⟩,
  ⟨"iteF", _,  if' (tlitn 0) then (tlitf 4.2) else (tlitf 2.4)⟩,
  -- more complex
  ⟨"vectorRange", _, (for' i:10 => i.i2n.n2f)⟩,
]
