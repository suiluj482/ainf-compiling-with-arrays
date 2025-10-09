import Polara.Tests.All

def main: IO Unit :=
  TmTest.print

-- #eval main

open Ty

#eval
  (
    let' f1 := (fun' a => (tlitf 2 * a) + tlitf 10);
    let' f2 := (fun' a => (tlitf 2 * a) + tlitf 11);
    (f1,, f2)
  ).toVPar

#eval
  (
    let' f1 := (fun' a => (tlitf 2 * a) + tlitf 10);
    let' f2 := (fun' a => (tlitf 2 * a) + tlitf 11);
    (f1,, f2)
  ).toAINF.cse

#eval
  (
    let' f1 := (for' i:5 => i.i2n + tlitn 10);
    let' f2 := (for' i:5 => i.i2n + tlitn 11);
    (f1,, f2)
  ).toAINF.toTm.normVPar

#eval (fun' c:nat => if' c then tlitf 1 else tlitf 2).toAINF.toTm.toVPar.normVPar

#eval (
    let' f1 := (fun' a => a + tlitf 2);
    let' f2 := (fun' a => a + tlitf 2);
    fun' a => (f1 @@ a) + (f2 @@ a)
  ).toAINF.toTm.toVPar.normVPar

#eval (
    let' f1 := (for' i:10 => i.i2n);
    let' f2 := (for' i:10 => i.i2n);
    fun' i => (f1[[i]]) + (f2[[i]])
  ).toAINF.toTm.toVPar
