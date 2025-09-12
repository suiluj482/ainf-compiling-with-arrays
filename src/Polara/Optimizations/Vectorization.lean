import Polara.Optimizations.Basics
import Polara.Optimizations.CleanEnv

private def vectorize' [t : BiArraysC BiArith α β γ](envPre envC envA envB: Env)(v: Var γ)(a: VPar α)(b: VPar β)(op: ArithOp): VParM Bnds :=
  match envPre with -- todo allow multiple forc
  | (.forc n i) :: env' => do
    let ar := (←VParM.var) (α.array n)
    let br := (←VParM.var) (β.array n)
    let cr := (←VParM.var) (γ.array n)
    return [
      -- env in val
      ⟨⟨_,ar⟩, (env'.append envA), Prim.bld i a⟩,
      ⟨⟨_,br⟩, (env'.append envB), Prim.bld i b⟩,
      -- vec op
      ⟨⟨_,cr⟩, (env'.append envC), Prim.cst2 (.arithOp op) (.v ar) (.v br)⟩,
      -- val in vec
      ⟨⟨_,v ⟩, (envPre.append envC) , Prim.cst2 (.get) (.v cr) (.p i)⟩
    ]
  | _ => pure [⟨⟨_,v⟩, (envPre.append envC), Prim.cst2 (.arithOp op) a b⟩]

def AINF.vectorize (ainf: AINF α): AINF α :=
  ainf.flatMapMBnd id (λ bnd => match bnd with
    | ⟨⟨α,v⟩,env,prim⟩ =>
      match prim with
      | .cst2 cst2 a b (α₁:=α') (α₂:=β') (α:=γ') =>
        match a, b with
        | .v av, .v bv =>
          let (envPrefix,restPrefixes) := #[
            env,
            av.lookupEnv ainf |>.get!,
            bv.lookupEnv ainf |>.get!,
          ].toVector.splitListPrefix
          let envR := restPrefixes[0]
          let aER := restPrefixes[1]
          let bER := restPrefixes[2]
          match cst2 with
          | .arithOp (type:=_) op =>
            -- vectorize' env
            match envPrefix with -- todo allow multiple forc
            | (.forc n i) :: env' => do
              let ar := (←VParM.var) (α'.array n)
              let br := (←VParM.var) (β'.array n)
              let cr := (←VParM.var) (γ'.array n)
              return [
                -- env in val
                ⟨⟨_,ar⟩, (env'.append aER), Prim.bld i a⟩,
                ⟨⟨_,br⟩, (env'.append bER), Prim.bld i b⟩,
                -- vec op
                ⟨⟨_,cr⟩, (env'.append envR), Prim.cst2 (.arithOp op) (.v ar) (.v br)⟩,
                -- val in vec
                ⟨⟨_,v ⟩, (env.append envR) , Prim.cst2 (.get) (.v cr) (.p i)⟩
              ]
            | _ => pure [bnd]
          | _ => pure [bnd]
        | _, _ => pure [bnd]
      | _ => pure [bnd]
  )

open Ty
#eval (for' i:10 => tlitf 1 + tlitf 1).toAINF.cleanEnv.vectorize -- no vecotrization
#eval (fun' a => for' i:10 => a[[i]] + (tlitf 1)).toAINF.cleanEnv.vectorize -- no vectorize?

#eval (fun' a: flt.array 10 => for' i:10 => a[[i]] + a[[i]]).toAINF.cleanEnv.vectorize -- vectorize
#eval (fun' a => for' i:10 => (a[[i]] + a[[i]]) + a[[i]]).toAINF.cleanEnv.vectorize -- vectorize

-- todo vecotrization gets optimized away by .toTm.normVPar
