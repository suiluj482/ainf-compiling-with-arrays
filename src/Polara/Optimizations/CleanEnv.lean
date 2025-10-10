import Polara.Syntax.All
import Polara.Optimizations.Convert.All

-- requires topological order
-- behavior:
-- - loop invariant codemotion
-- - loop unswitching

private def Env.clean (reqPars: List (Sigma Par))(reqEnvParts: List EnvPart)(ites: List (VPar .nat × Bool × (Par .nat ⊕ Env)))(env: Env): ReaderM Bnds Env :=
  match env with
  | [] => return ites.map (λ (c,b,_) => .itec c b)
  | envPart :: env' => do match envPart with
    | .func _ p
    | .forc _ p =>
        let (reqItes, ites) := ites.seperateBy (λ -- seperate if itec is required to be in envPart
            | (_,_, .inl par) => if t: p.type = .nat then t▸p == par else false
            | (_,_, .inr env) => env.contains envPart
          )
        if -- envPart is required (loop&func invariant code motion)
          !reqItes.isEmpty           -- needed for an ites
          ∨ reqPars.contains ⟨_,p⟩      -- paramter bound by envPart is needed
          ∨ reqEnvParts.contains envPart -- needed for the env of a used var
        then
          let itecs := reqItes.map (λ (c,b,_) => EnvPart.itec c b)
          let pars'    := reqItes.filterMap (λ | (_,_, .inl p) => some ⟨_,p⟩ | _ => none) |>.foldl (·.addToSet ·) reqPars
          let reqEnvs' := reqItes.filterMap (λ | (_,_, .inr e) => some e     | _ => none) |>.foldl (·.combineSets ·) reqEnvParts
          return itecs.append (envPart :: (←clean pars' reqEnvs' ites env'))
        else clean reqPars reqEnvParts ites env'
    | .itec c b => -- buffer in ites until end or required (loop&func unswitching)
        match c with
        | .v v =>
            let env := (←v.lookupEnvRB).get!
            clean reqPars reqEnvParts (ites.concat (c,b, .inr env)) env'
        | .p p =>
            clean reqPars reqEnvParts (ites.concat (c,b, .inl p  )) env'

private def Bnds.cleanEnv (res: Bnds): Bnds → Bnds
| [] => res
| bnd :: bnds' =>
  let ⟨⟨_,v⟩,env,prim⟩ := bnd

  let pars    := prim.pars
  let reqEnvs := prim.vars.map (λ ⟨_,v⟩ => (v.lookupEnvB res).get!) |>.foldl (·.combineSets ·) []

  let env' := env.clean pars reqEnvs [] res
  Bnds.cleanEnv (res.concat ⟨⟨_,v⟩,env',prim⟩) bnds'

def AINF.cleanEnv: AINF α → AINF α :=
  AINF.mapBnds (Bnds.cleanEnv [])


-- open Ty
-- -- loop invariant code motion
-- #eval (for' i:10 => (tlitf 1) + (tlitf 1)).toAINF.cleanEnv
-- #eval (for' i:10 => (tlitf 1) + i.i2n.n2f).toAINF.cleanEnv
-- -- loop required for if
-- #eval (for' i:10 => if' i.i2n then (tlitf 0) else (tlitf 1)).toAINF.cleanEnv
-- -- loop unswitching
-- #eval (for' i:10 => for' j:10 => if' i.i2n then (tlitf 0) else j.i2n.n2f).toAINF.cleanEnv
