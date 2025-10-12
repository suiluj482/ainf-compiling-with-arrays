import Polara.Codegeneration.All
import Polara.Optimizations.All
import Polara.AD.All
import Polara.Tests.Examples.All

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
        leaf ⟨"exp",  _,_,    (tlitf 4.2).exp, id, some <| Float.exp 4.2⟩,
        leaf ⟨"sqrt", _,_,    (tlitf 4.2).sqrt, id, some <| Float.sqrt 4.2⟩,
        leaf ⟨"log",  _,_,    (tlitf 4.2).log, id, some <| Float.log 4.2⟩,
        leaf ⟨"normCdf", _,_, (tlitf 4.2).normCdf.le, id, some <| Float.normCdf 4.2⟩,
        leaf ⟨"fst", _,_,    ((tlitf 4.2),, (tlitf 3.14)).fst, id, some 4.2⟩,
        leaf ⟨"snd", _,_,    ((tlitf 4.2),, (tlitf 3.14)).snd, id, some 3.14⟩,
        leaf ⟨"sum", _,_,    (for'v _:10 => tlitf 4.2).sumf, id, some 42⟩,
        leaf ⟨"i2n", _,_,    (tliti (2: Fin 6)).i2n, id, some 2⟩,
        leaf ⟨"n2f", _,_,    (tlitn 42).n2f, id, some 42⟩,
        -- cst2
        leaf ⟨"addn", _,_,  (tlitn 42) + (tlitn 2), id, some 44⟩,
        leaf ⟨"subn", _,_,  (tlitn 42) - (tlitn 2), id, some 40⟩,
        leaf ⟨"muln", _,_,  (tlitn 42) * (tlitn 2), id, some 84⟩,
        leaf ⟨"divn", _,_,  (tlitn 42) / (tlitn 2), id, some 21⟩,
        leaf ⟨"addf", _,_,  (tlitf 42.0) + (tlitf 2.0), id, some 44⟩,
        leaf ⟨"subf", _,_,  (tlitf 42.0) - (tlitf 2.0), id, some 40⟩,
        leaf ⟨"mulf", _,_,  (tlitf 42.0) * (tlitf 2.0), id, some 84⟩,
        leaf ⟨"divf", _,_,  (tlitf 42.0) / (tlitf 2.0), id, some 21⟩,
        leaf ⟨"adda", _,_,  (for'v _:10 => tlitf 4.2) + (for'v _:10 => tlitf 2.0), id, some (Vector.replicate 10 6.2)⟩,
        leaf ⟨"suba", _,_,  (for'v _:10 => tlitf 4.2) - (for'v _:10 => tlitf 2.0), id, some (Vector.replicate 10 2.2)⟩,
        leaf ⟨"mula", _,_,  (for'v _:10 => tlitf 4.2) * (for'v _:10 => tlitf 2.0), id, some (Vector.replicate 10 8.4)⟩,
        leaf ⟨"diva", _,_,  (for'v _:10 => tlitf 4.2) / (for'v _:10 => tlitf 2.0), id, some (Vector.replicate 10 2.1)⟩,
        leaf ⟨"addi", _,_,  (tliti (2: Fin 8)).addi (tliti (3: Fin 4)), id, some ⟨5,by simp⟩⟩,
        leaf ⟨"eqi",  _,_,  (tliti (2: Fin 3)).eqi (tliti (2: Fin 3)), id, some 1⟩,
        leaf ⟨"maxf", _,_,  (tlitf 42.0).maxf (tlitf 2.0), id, some 42⟩,
        leaf ⟨"lt", _,_,    (tlitf 42.0) <' (tlitf 2.0), id, some 0⟩,
        leaf ⟨"get", _,_,   (for'v _:10 => tlitf 4.2)[[(tliti (2: Fin 11))]], id, some 4.2⟩,
        leaf ⟨"tup", _,_,   ((tlitf 4.2),, (tlitn 42)), id, some (4.2, 42)⟩,
        leaf ⟨"app", _,_,   (fun'v _:nat => tlitf 4.2) @@ (tlitn 42), id, some (4.2)⟩,
        -- tm
        leaf ⟨"var", _,_,   let' v := tlitf 4.2; v, id, some 4.2⟩,
        leaf ⟨"abs", _,_,   (fun'v _:nat => tlitf 4.2), (·@@ (tlitn 42)), some 4.2⟩,
        leaf ⟨"bld", _,_,   for'v _:10 => tlitf 4.2, id, some (Vector.replicate 10 4.2)⟩,
        leaf ⟨"iteT", _,_,  if' (tlitn 1) then (tlitf 4.2) else (tlitf 2.4), id, some 4.2⟩,
        leaf ⟨"iteF", _,_,  if' (tlitn 0) then (tlitf 4.2) else (tlitf 2.4), id, some 2.4⟩,
      ],
      node "Simple" [
        leaf ⟨"vectorRange", _,_, (for' i:10 => i.i2n.n2f), id, some <| Vector.ofFn (λ i => i.val.toFloat)⟩,
      ],
      node "AD" [
        node "dualNumbers" [
          -- literals
          leaf ⟨"litnat", _,_,
            (tlitn 42).aD.le, id,
            some 42
          ⟩,
          leaf ⟨"litflt", _,_,
            (tlitf 3.14).aD.le, id,
            some (3.14, 0)
          ⟩,
          -- func
          leaf ⟨"id", _,_,
            (fun' x:flt => x).aD.le, (·@@ (tlitf 3.14,, tlitf 1.0)),
            some (3.14, 1.0)
          ⟩,
          -- cst1
          leaf ⟨"exp", _,_,
            (fun' x:flt => x.exp).aD.le, (·@@ (tlitf 0.0,, tlitf 1.0)),
            some (1.0, 1.0)
          ⟩,
          leaf ⟨"log", _,_,
            (fun' x:flt => x.log).aD.le, (·@@ (tlitf 1.0,, tlitf 1.0)),
            some (0.0, 1.0)
          ⟩,
          leaf ⟨"sqrt", _,_,
            (fun' x:flt => x.sqrt).aD.le, (·@@ (tlitf 4.0,, tlitf 1.0)),
            some (2.0, 0.25)
          ⟩,
          leaf ⟨"normCdf", _,_,
            (fun' x:flt => x.normCdf).aD.le, (·@@ (tlitf 0.0,, tlitf 1.0)),
            some (0.5, 0.3989422804)
          ⟩,
          leaf ⟨"fst", _,_,
            (fun' x:(flt ×× flt) => x.fst).aD.le,
            (·@@ ((tlitf 4.2,, tlitf 0.0),, (tlitf 3.14,, tlitf 1.0))),
            some (4.2, 0.0)
          ⟩,
          leaf ⟨"snd", _,_,
            (fun' x:(flt ×× flt) => x.snd).aD.le,
            (·@@ ((tlitf 4.2,, tlitf 0.0),, (tlitf 3.14,, tlitf 1.0))),
            some (3.14, 1.0)
          ⟩,
          leaf ⟨"sumf", _,_,
            (fun' x:(array 10 flt) => x.sumf).aD.le,
            (·@@ (for' i:10 => (tlitf 4.2,, tlitf 1.0))),
            some (42.0, 10.0)
          ⟩,
          leaf ⟨"n2f", _,_,
            (fun' x:nat => x.n2f).aD.le,
            (·@@ (tlitn 42)),
            some (42.0, 0.0)
          ⟩,
          -- cst2
          leaf ⟨"add", _,_,
            (fun' x:flt => fun' y:flt => x + y).aD.le,
            (·@@ (tlitf 40.0,, tlitf 1.0) @@ (tlitf 2.0,, tlitf 2.0)),
            some (42.0, 3.0)
          ⟩,
          leaf ⟨"sub", _,_,
            (fun' x:flt => fun' y:flt => x - y).aD.le,
            (·@@ (tlitf 44.0,, tlitf 1.0) @@ (tlitf 2.0,, tlitf 2.0)),
            some (42.0, -1.0)
          ⟩,
          leaf ⟨"mul", _,_,
            (fun' x:flt => fun' y:flt => x * y).aD.le,
            (·@@ (tlitf 21.0,, tlitf 1.0) @@ (tlitf 2.0,, tlitf 2.0)),
            some (42.0, 44.0)
          ⟩,
          leaf ⟨"div", _,_,
            (fun' x:flt => fun' y:flt => x / y).aD.le,
            (·@@ (tlitf 84.0,, tlitf 1.0) @@ (tlitf 2.0,, tlitf 2.0)),
            some (42.0, -41.5)
          ⟩,
          leaf ⟨"adda", _,_,
            (fun' x:(array 10 flt) => fun' y:(array 10 flt) => x + y).aD.le,
            (·@@ (for' i:10 => (tlitf 40.0,, tlitf 1.0)) @@ (for' i:10 => (tlitf 2.0,, tlitf 2.0))),
            some (Vector.replicate 10 (42.0, 3.0))
          ⟩,
          leaf ⟨"maxf", _,_,
            (fun' x:flt => fun' y:flt => x.maxf y).aD.le,
            (·@@ (tlitf 40.0,, tlitf 1.0) @@ (tlitf 42.0,, tlitf 2.0)),
            some (42.0, 2.0)
          ⟩,
          -- higher order functions
          leaf ⟨"curried", _,_,
            (fun' x:flt => fun' y:flt => x + y).aD.le,
            (·@@ (tlitf 4.0,, tlitf 1.0) @@ (tlitf 2.0,, tlitf 0.0)),
            some (6.0, 1.0)
          ⟩,
          leaf ⟨"curried2", _,_,
            (fun' x:flt => fun' y:flt => fun' z:flt => x + y).aD.le,
            (·@@ (tlitf 4.0,, tlitf 1.0) @@ (tlitf 2.0,, tlitf 0.0) @@ (tlitf 100.0,, tlitf 0.0)),
            some (6.0, 1.0)
          ⟩,
          leaf ⟨"higherorder", _,_,
            (fun' f:(flt ~> flt) => fun' x:flt => (tlitf 1.0) + (f @@ x)).aD.le,
            (·@@ (fun' y:flt××flt => (y.fst + (tlitf 1.0),, y.snd)) -- (·+1)
              @@ (tlitf 3.0,, tlitf 1.0)),
            some (5.0, 1.0)
          ⟩,
          leaf ⟨"letBeforeFun", _,_,
            (let' v := tlitf 0; fun'v _:nat => v).aD.le,
            (·@@ (tlitn 0)),
            some (0, 0)
          ⟩,
          leaf ⟨"letBeforeAD", _,_,
            (let' v := tlitf 0; (fun'v _:nat => v).aD).le,
            (·@@ tlitn 0),
            some (0, 0)
          ⟩,
        ],
        node "df" [
          -- literals
          leaf ⟨"litnat", _,_,
            (tlitn 42).df.le, id,
            some 42
          ⟩,
          leaf ⟨"litflt", _,_,
            (tlitf 3.14).df.le, id,
            some 3.14
          ⟩,
          -- func
          leaf ⟨"id", _,_,
            (fun' x:flt => x).df.le, (let't v, d := ·@@ tlitf 3.14; (v,, d@@ tlitf 1.0)),
            some (3.14, 1.0)
          ⟩,
          leaf ⟨"twoDfEval", _,_,
            (fun' x:flt××flt => x.fst + x.snd).df.le,
            (let't v, d := ·@@ (tlitf 3.0,, tlitf 4.0);
              (v,,
                (d@@ (tlitf 1.0,, tlitf 0.0),,
                 d@@ (tlitf 0.0,, tlitf 1.0))
              )),
            some (7.0, (1.0, 1.0))
          ⟩,
          -- cst1
          leaf ⟨"exp", _,_,
            (fun' x:flt => x.exp).df.le,
            (let't v, d := ·@@ tlitf 0.0; (v,, d@@ tlitf 1.0)),
            some (1.0, 1.0)
          ⟩,
          leaf ⟨"log", _,_,
            (fun' x:flt => x.log).df.le,
            (let't v, d := ·@@ tlitf 1.0; (v,, d@@ tlitf 1.0)),
            some (0.0, 1.0)
          ⟩,
          leaf ⟨"sqrt", _,_,
            (fun' x:flt => x.sqrt).df.le,
            (let't v, d := ·@@ tlitf 4.0; (v,, d@@ tlitf 1.0)),
            some (2.0, 0.25)
          ⟩,
          leaf ⟨"normCdf", _,_,
            (fun' x:flt => x.normCdf).df.le,
            (let't v, d := ·@@ tlitf 0.0; (v,, d@@ tlitf 1.0)),
            some (0.5, 0.3989422804)
          ⟩,
          leaf ⟨"fst", _,_,
            (fun' x:(flt ×× flt) => x.fst).df.le,
            (let't v, d := ·@@ (tlitf 4.2,, tlitf 3.14); (v,, d@@ (tlitf 0.0,, tlitf 1.0))),
            some (4.2, 0.0)
          ⟩,
          leaf ⟨"snd", _,_,
            (fun' x:(flt ×× flt) => x.snd).df.le,
            (let't v, d := ·@@ (tlitf 4.2,, tlitf 3.14); (v,, d@@ (tlitf 0.0,, tlitf 1.0))),
            some (3.14, 1.0)
          ⟩,
          leaf ⟨"sumf", _,_,
            (fun' x:(array 10 flt) => x.sumf).df.le,
            (let't v, d := ·@@ (for' i:10 => tlitf 4.2); (v,, d@@ (for' i:10 => tlitf 1.0))),
            some (42.0, 10.0)
          ⟩,
          leaf ⟨"n2f", _,_,
            (fun' x:nat => x.n2f).df.le,
            (let't v, d := ·@@ tlitn 42; (v,, d@@ ()')),
            some (42.0, 0.0)
          ⟩,
          leaf ⟨"n2fRmUnits", _,_,
            (fun' x:nat => x.n2f).df.rmUnits,
            (let't v, d := ·@@ tlitn 42; (v,, d)),
            some (42.0, 0.0)
          ⟩,
          -- cst2
          leaf ⟨"add", _,_,
            (fun' x:flt => fun' y:flt => x + y).df.le,
            (let't t, dx := ·@@ tlitf 40.0;
             let' y := tlitf 2.0;
             let't v, dy := t@@ y;
             (v,, (dx@@ tlitf 1.0 @@ y,, dy@@ tlitf 1.0))),
            some (42.0, (1.0, 1.0))
          ⟩,
          leaf ⟨"sub", _,_,
            (fun' x:flt => fun' y:flt => x - y).df.le,
            (let't t, dx := ·@@ tlitf 44.0;
             let' y := tlitf 2.0;
             let't v, dy := t@@ y;
             (v,, (dx@@ tlitf 1.0 @@ y,, dy@@ tlitf 1.0))),
            some (42.0, (1.0, -1.0))
          ⟩,
          leaf ⟨"mul", _,_,
            (fun' x:flt => fun' y:flt => x * y).df.le,
            (let't t, dx := ·@@ tlitf 44.0;
             let' y := tlitf 2.0;
             let't v, dy := t@@ y;
             (v,, (dx@@ tlitf 1.0 @@ y,, dy@@ tlitf 1.0))),
            some (88.0, (2.0, 44.0))
          ⟩,
          leaf ⟨"div", _,_,
            (fun' x:flt => fun' y:flt => x / y).df.le,
            (let't t, dx := ·@@ tlitf 44.0;
             let' y := tlitf 2.0;
             let't v, dy := t@@ y;
             (v,, (dx@@ tlitf 1.0 @@ y,, dy@@ tlitf 1.0))),
            some (22.0, (0.5, -11.0))
          ⟩,
          leaf ⟨"adda", _,_,
            (fun' x:(array 10 flt) => fun' y:(array 10 flt) => x + y).df.le,
            (let't t, dx := ·@@ (for' i:10 => tlitf 40.0);
             let' y := (for' i:10 => tlitf 2.0);
             let't v, dy := t@@ y;
             (v,, (dx@@ (for' i:10 => tlitf 1.0) @@ y,, dy@@ (for' i:10 => tlitf 1.0)))),
            some ((Vector.replicate 10 42.0), (Vector.replicate 10 1.0, Vector.replicate 10 1.0))
          ⟩,
          leaf ⟨"maxf", _,_,
            (fun' x:flt => fun' y:flt => x.maxf y).df.le,
            (let't t, dx := ·@@ tlitf 40.0;
             let' y := tlitf 42.0;
             let't v, dy := t@@ y;
             (v,, (dx@@ tlitf 1.0 @@ y,, dy@@ tlitf 1.0))),
            some (42.0, (0.0, 1.0))
          ⟩,
          -- higher order functions
          leaf ⟨"curried", _,_,
            (fun' x:flt => fun' y:flt => x + y).df.le,
            (let't t, dx := ·@@ tlitf 4.0;
             let' y := tlitf 2.0;
             let't v, dy := t@@ y;
             (v,, (dx@@ tlitf 1.0 @@ y,, dy@@ tlitf 1.0))),
            some (6.0, (1.0, 1.0))
          ⟩,
          leaf ⟨"curried2", _,_,
            (fun' x:flt => fun' y:flt => fun' z:flt => x + y).df.le,
            (let't t, dx := ·@@ tlitf 4.0;
             let' y := tlitf 2.0;
             let't t, dy := t@@ y;
             let' z := tlitf 100.0;
             let't v, dz := t@@ z;
             (v,, (dx@@ tlitf 1.0 @@ y @@ z,, (dy@@ tlitf 1.0 @@ y,, dz@@ tlitf 1.0)))),
            some (6.0, (1.0, 1.0, 0.0))
          ⟩,
          leaf ⟨"higherorder", _,_,
            (fun' f:(flt ~> flt) => fun' x:flt => (tlitf 1.0) + (f @@ x)).df.le,
            (let't t, _ := ·@@ (fun' y:flt => (y + tlitf 1.0,, fun' dy => dy)); -- (·+1)
             let' x := (tlitf 4.0);
             let't v, dx := t@@ x;
             (v,, dx@@ tlitf 1.0)),
            some (6.0, 1.0)
          ⟩,
          leaf ⟨"letBeforeFun", _,_,
            (let' v := tlitf 0; fun'v _:nat => v).df.le,
            (let't v,d := ·@@ (tlitn 0); (v,, d@@ ()')),
            some (0, 0)
          ⟩,
          leaf ⟨"forBeforeFun", _,_,
            (for' a:2 => fun'v _:nat => a).df.le,
            (for' a:2 => let't v,d := ·[[a]]@@ (tlitn 0); (v,, d@@ ()')),
            some  #[(0, ()), (1,())].toVector
          ⟩,
          leaf ⟨"letBeforeAD", _,_,
            (let' v := tlitf 0; (fun'v _:nat => v).df).le,
            (let't v,d := ·@@ (tlitn 0); (v,, d@@ ()')),
            some (0, 0)
          ⟩,
        ],
        node "dr" [
          -- literals
          leaf ⟨"litnat", _,_,
            (tlitn 42).dr.le, id,
            some 42
          ⟩,
          leaf ⟨"litflt", _,_,
            (tlitf 3.14).dr.le, id,
            some 3.14
          ⟩,
          -- func
          leaf ⟨"id", _,_,
            (fun' x:flt => x).dr.le, (let't v, d := ·@@ tlitf 3.14; (v,, d@@ tlitf 1.0)),
            some (3.14, 1.0)
          ⟩,
          leaf ⟨"twoDfEval", _,_,
            (fun' x:flt××flt => x.fst + x.snd).dr.le,
            (let't v, d := ·@@ (tlitf 3.0,, tlitf 4.0);
              (v,, d@@ tlitf 1.0)),
            some (7.0, (1.0, 1.0))
          ⟩,
          -- cst1
          leaf ⟨"exp", _,_,
            (fun' x:flt => x.exp).dr.le,
            (let't v, d := ·@@ tlitf 0.0; (v,, d@@ tlitf 1.0)),
            some (1.0, 1.0)
          ⟩,
          leaf ⟨"log", _,_,
            (fun' x:flt => x.log).dr.le,
            (let't v, d := ·@@ tlitf 1.0; (v,, d@@ tlitf 1.0)),
            some (0.0, 1.0)
          ⟩,
          leaf ⟨"sqrt", _,_,
            (fun' x:flt => x.sqrt).dr.le,
            (let't v, d := ·@@ tlitf 4.0; (v,, d@@ tlitf 1.0)),
            some (2.0, 0.25)
          ⟩,
          leaf ⟨"normCdf", _,_,
            (fun' x:flt => x.normCdf).dr.le,
            (let't v, d := ·@@ tlitf 0.0; (v,, d@@ tlitf 1.0)),
            some (0.5, 0.3989422804)
          ⟩,
          leaf ⟨"fst", _,_,
            (fun' x:(flt ×× flt) => x.fst).dr.le,
            (let't v, d := ·@@ (tlitf 4.2,, tlitf 3.14); (v,, d@@ tlitf 1.0)),
            some (4.2, (1.0, 0.0))
          ⟩,
          leaf ⟨"snd", _,_,
            (fun' x:(flt ×× flt) => x.snd).dr.le,
            (let't v, d := ·@@ (tlitf 4.2,, tlitf 3.14); (v,, d@@ tlitf 1.0)),
            some (3.14, (0.0, 1.0))
          ⟩,
          leaf ⟨"sumf", _,_,
            (fun' x:(array 10 flt) => x.sumf).dr.le,
            (let't v, d := ·@@ (for' i:10 => tlitf 4.2); (v,, d@@ tlitf 1.0)),
            some (42.0, Vector.replicate 10 1.0)
          ⟩,
          leaf ⟨"n2f", _,_,
            (fun' x:nat => x.n2f).dr.le,
            (let't v, d := ·@@ tlitn 42; (v,, d@@ tlitf 1.0)),
            some (42.0, ())
          ⟩,
          leaf ⟨"n2fRmUnits", _,_,
            (fun' x:nat => x.n2f).dr.rmUnits,
            (·@@ tlitn 42),
            some (42.0)
          ⟩,
          -- cst2
          leaf ⟨"add", _,_,
            (fun' x:flt => fun' y:flt => x + y).dr.le,
            (let't t, dx := ·@@ tlitf 40.0;
             let' y := tlitf 2.0;
             let't v, dy := t@@ y;
             (v,, (dx@@ (y,, tlitf 1.0),, dy@@ tlitf 1.0))),
            some (42.0, (1.0, 1.0))
          ⟩,
          leaf ⟨"sub", _,_,
            (fun' x:flt => fun' y:flt => x - y).dr.le,
            (let't t, dx := ·@@ tlitf 44.0;
             let' y := tlitf 2.0;
             let't v, dy := t@@ y;
             (v,, (dx@@ (y,, tlitf 1.0),, dy@@ tlitf 1.0))),
            some (42.0, (1.0, -1.0))
          ⟩,
          leaf ⟨"mul", _,_,
            (fun' x:flt => fun' y:flt => x * y).dr.le,
            (let't t, dx := ·@@ tlitf 44.0;
             let' y := tlitf 2.0;
             let't v, dy := t@@ y;
             (v,, (dx@@ (y,, tlitf 1.0),, dy@@ tlitf 1.0))),
            some (88.0, (2.0, 44.0))
          ⟩,
          leaf ⟨"div", _,_,
            (fun' x:flt => fun' y:flt => x / y).dr.le,
            (let't t, dx := ·@@ tlitf 44.0;
             let' y := tlitf 2.0;
             let't v, dy := t@@ y;
             (v,, (dx@@ (y,, tlitf 1.0),, dy@@ tlitf 1.0))),
            some (22.0, (0.5, -11.0))
          ⟩,
          leaf ⟨"adda", _,_,
            (fun' x:(array 10 flt) => fun' y:(array 10 flt) => x + y).dr.le,
            (let't t, dx := ·@@ (for' i:10 => tlitf 40.0);
             let' y := (for' i:10 => tlitf 2.0);
             let't v, dy := t@@ y;
             (v,, (dx@@ (y,, (for' i:10 => tlitf 1.0)),, dy@@ (for' i:10 => tlitf 1.0)))),
            some ((Vector.replicate 10 42.0), (Vector.replicate 10 1.0, Vector.replicate 10 1.0))
          ⟩,
          leaf ⟨"maxf", _,_,
            (fun' x:flt => fun' y:flt => x.maxf y).dr.le,
            (let't t, dx := ·@@ tlitf 40.0;
             let' y := tlitf 42.0;
             let't v, dy := t@@ y;
             (v,, (dx@@ (y,, tlitf 1.0),, dy@@ tlitf 1.0))),
            some (42.0, (0.0, 1.0))
          ⟩,
          -- higher order functions
          leaf ⟨"curried", _,_,
            (fun' x:flt => fun' y:flt => x + y).dr.le,
            (let't t, dx := ·@@ tlitf 4.0;
             let' y := tlitf 2.0;
             let't v, dy := t@@ y;
             (v,, (dx@@ (y,, tlitf 1.0),, dy@@ tlitf 1.0))),
            some (6.0, (1.0, 1.0))
          ⟩,
          leaf ⟨"curried2", _,_,
            (fun' x:flt => fun' y:flt => fun' z:flt => x + y).dr.le,
            (let't t, dx := ·@@ tlitf 4.0;
             let' y := tlitf 2.0;
             let't t, dy := t@@ y;
             let' z := tlitf 100.0;
             let't v, dz := t@@ z;
             (v,, (dx@@ (y,, (z,, tlitf 1.0)),, (dy@@ (y,, tlitf 1.0),, dz@@ tlitf 1.0)))),
            some (6.0, (1.0, 1.0, 0.0))
          ⟩,
          leaf ⟨"higherorder", _,_,
            (fun' f:(flt ~> flt) => fun' x:flt => (tlitf 1.0) + (f @@ x)).dr.le,
            (let't t, _ := ·@@ (fun' y:flt => (y + tlitf 1.0,, fun' dy => dy)); -- (·+1)
             let' x := (tlitf 4.0);
             let't v, dx := t@@ x;
             (v,, dx@@ tlitf 1.0)),
            some (6.0, 1.0)
          ⟩,
          leaf ⟨"letBeforeFun", _,_,
            (let' v := tlitf 0; fun'v _:nat => v).dr.le,
            (let't v,d := ·@@ (tlitn 0); (v,, d@@ tlitf 0)),
            some (0, ())
          ⟩,
          leaf ⟨"forBeforeFun", _,_,
            (for' a:2 => fun'v _:nat => a).dr.le,
            (for' a:2 => let't v,d := ·[[a]]@@ (tlitn 0); (v,, d@@ ()')),
            some  #[(0, ()), (1,())].toVector
          ⟩,
          leaf ⟨"letBeforeAD", _,_,
            (let' v := tlitf 0; (fun'v _:nat => v).dr).le,
            (let't v,d := ·@@ (tlitn 0); (v,, d@@ tlitf 0)),
            some (0, ())
          ⟩,
        ],
      ],
      node "examplesCompilingWithArrays" [
        leaf ⟨"mainBlackScholes10", _,_,
          mainBlackScholes,
          (· @@ (for' i:10 => i.i2n.n2f)),
          none
        ⟩,
        leaf ⟨"mainBlackScholes100", _,_,
          mainBlackScholes,
          (· @@ (for' i:100 => i.i2n.n2f)),
          none
        ⟩,
        leaf ⟨"dense", _,_,
          dense 10 20,
          (· @@ (for' i => i.i2n.n2f)
             @@ (for' i => for' j => i.i2n.n2f + j.i2n.n2f)
             @@ (for' j => j.i2n.n2f)
          ),
          none
        ⟩,
        leaf ⟨"conv", _,_,
          conv 10 20,
          (· @@ (for' i => i.i2n.n2f)
             @@ (for' i => i.i2n.n2f)
          ),
          none
        ⟩,
        leaf ⟨"loop1", _,_,
          loop1 10,
          id,
          none
        ⟩,
        leaf ⟨"foo", _,_,
          foo,
          (· @@ (for' i:10 => i.i2n)),
          none
        ⟩,
        leaf ⟨"cseTest1", _,_,
          cseTest1,
          (· @@ (tlitn 0)),
          none
        ⟩,
        leaf ⟨"cseTest2", _,_,
          cseTest2,
          (· @@ (tlitn 0)),
          none
        ⟩,
        leaf ⟨"cseTest3", _,_,
          cseTest3,
          (· @@ (tlitn 0)),
          none
        ⟩,
        leaf ⟨"egypt5", _,_,
          egypt 5,
          (· @@ (tlitn 0)),
          none
        ⟩,
      ],
      node "examplesThesis" [
        node "cse" [

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
        | none => .inr s!"{fullName}{name}: no value: {mes}"
      )
    let errors := errors ++ match expected with
      | some expected =>
        flat.filterMap (λ (name, val, mes) =>
            if α.similarVal expected val
              then none
              else some s!"{fullName}{name}: expected: {expected}, got: {mes}"
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
