import Polara.Optimizations.Basics
import Polara.Optimizations.CleanEnv

-- vectorizes arithOps that are all in the same forc envParts
--   note doesn't vectorize lin ops

private def vectorize' [t : BiArraysC BiArith α β γ](envPre envC envA envB: Env)(c: Var γ)(a: VPar α)(b: VPar β)(op: ArithOp): VParM Bnds :=
  match envPre with
  | (.forc n i) :: envPre' => do
    let ar := (←VParM.var) (α.array n)
    let br := (←VParM.var) (β.array n)
    let cr := (←VParM.var) (γ.array n)
    return [
        -- env in val
        ⟨⟨_,ar⟩, (envPre'.append envA), Prim.bld i a⟩,
        ⟨⟨_,br⟩, (envPre'.append envB), Prim.bld i b⟩,
      ]
      ++ -- recursive
        (←(vectorize' envPre' envC envA envB cr (.v ar) (.v br) op))
      ++ [
        -- val in vec
        ⟨⟨_,c ⟩, (envPre.append envC) , Prim.cst2 (.get) (.v cr) (.p i)⟩
      ]
  | _ => return [
      -- actual operation
      ⟨⟨_,c⟩, (envPre.append envC), Prim.cst2 (.arithOp op) a b⟩
    ]

def AINF.vectorize (ainf: AINF α): AINF α :=
  ainf.flatMapMBnd id (λ bnd => match bnd with
    | ⟨⟨α,v⟩,env,prim⟩ =>
      match prim with
      | .cst2 cst2 a b (α₁:=α') (α₂:=β') (α:=γ') =>
        match a, b with
        | .v av, .v bv =>
          match cst2 with
          | .arithOp (type:=_) op =>
            let (envPrefix,restPrefixes) := #[
              env,
              av.lookupEnv ainf |>.get!,
              bv.lookupEnv ainf |>.get!,
            ].toVector.splitListPrefix
            let cER := restPrefixes[0]
            let aER := restPrefixes[1]
            let bER := restPrefixes[2]
            vectorize' envPrefix cER aER bER v a b op
          | _ => pure [bnd]
        | _, _ => pure [bnd]
      | _ => pure [bnd]
  )

-- open Ty
-- -- no vecotrize: not dependent on forc
-- #eval (for' i:10 => tlitf 1 + tlitf 1).toAINF.cleanEnv.vectorize
-- -- no vectorize: only partly dependent on forc
-- #eval (fun' a => for' i:10 => a[[i]] + (tlitf 1)).toAINF.cleanEnv.vectorize

-- -- vectorize
-- #eval (fun' a => for' i:10 => a[[i]] + a[[i]]).toAINF.cleanEnv.vectorize
-- -- vectorize: multiple ops
-- #eval (fun' a => for' i:10 => (a[[i]] + a[[i]]) + a[[i]]).toAINF.cleanEnv.vectorize
-- -- vectorize: multiple forc
-- #eval (fun' a => for' i:10 => for' j:10 => a[[i]][[j]] + a[[i]][[j]]).toAINF.cleanEnv.vectorize
