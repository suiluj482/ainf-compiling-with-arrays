import Polara.Syntax.All
import Polara.Optimizations.Convert.All

-- loop invariant codemotion

-- requires topological order
def Bnds.cleanEnv (res: Bnds): Bnds → Bnds
| [] => res
| bnd :: bnds' =>
  let ⟨⟨_,v⟩,env,prim⟩ := bnd
  let pars := Bnd.pars bnd
  let vars := Bnd.vars bnd
  let defsEnv: List EnvPart := vars.flatMap (λ ⟨_,v⟩ => (v.lookupEnvB res).get!) -- remove duplicates?
  let env' := env.filter (λ
    -- an envPart isn't needed if its par isn't directly used or used by a required def
    | .func _ x => pars.contains ⟨_,x⟩ ∨ defsEnv.contains (.func _ x)
    | .forc _ i => pars.contains ⟨_,i⟩ ∨ defsEnv.contains (.forc _ i)
    | .itec _ _ => true -- itec always good to have
  )
  Bnds.cleanEnv (res.concat ⟨⟨_,v⟩,env',prim⟩) bnds'

def AINF.cleanEnv: AINF α → AINF α
| (bnds, ret) => (Bnds.cleanEnv [] bnds, ret)


open Ty
#eval (for' i:10 => (tlitf 1) + (tlitf 1)).toAINF.cleanEnv
#eval (for' i:10 => (tlitf 1) + i.i2n.n2f).toAINF.cleanEnv
#eval (for' i:10 => if' i.i2n then (tlitf 0) else (tlitf 1)).toAINF.cleanEnv

-- todo push itec as far back as possible? (loop unswitching)
#eval (for' i:10 => for' j:10 => if' i.i2n then (tlitf 0) else j.i2n.n2f).toAINF.cleanEnv
