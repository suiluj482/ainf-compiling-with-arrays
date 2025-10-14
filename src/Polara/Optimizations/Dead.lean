import Polara.Syntax.All

-- Dead Code Elimination

open Std

private def Bnds.dead(marked: HashMap (Sigma Var) Unit): Bnds → Bnds
| [] => []
| bnd :: bnds =>
    if marked.contains (Bnd.var bnd) then
      let marked := marked.insertMany (Bnd.vars bnd |>.map (·,()))
      bnd :: dead marked bnds
    else dead marked bnds

def AINF.dead: AINF α → AINF α
| (bnds, ret) => (
    let marked := Singleton.singleton (⟨_,ret⟩,())
    (Bnds.dead marked bnds.reverse).reverse,
    ret
  )
