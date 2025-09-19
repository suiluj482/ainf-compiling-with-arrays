import Polara.Syntax.All

-- Dead Code Elimination

open Std

private def Bnds.dead(marked: HashMap (Sigma Var) Unit): Bnds → Bnds
| [] => []
| bnd :: bnds =>
    let ⟨v,_,prim⟩ := bnd
    if marked.contains v then
      let marked := marked.insertMany (prim.vars |>.map (·,()))
      bnd :: dead marked bnds
    else dead marked bnds

def AINF.dead: AINF α → AINF α
| (bnds, ret) => (
    match ret with
    | .p _ => panic! "return of AINF can't be param"
    | .v ret =>
      let marked := Singleton.singleton (⟨_,ret⟩,())
      (Bnds.dead marked bnds.reverse).reverse,
    ret
  )
