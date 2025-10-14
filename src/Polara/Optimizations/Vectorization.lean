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

-- devectorize Tm
private def ArithOp.devec [t: BiArraysC BiArith α β γ](op: ArithOp)
  (a: Tm Γ α)(b: Tm Γ β): Tm Γ γ :=
   match t.t with
  | .array n t' =>
      have: BiArraysC BiArith _ _ _ := ⟨t'⟩
      for' i => (ArithOp.devec op a[[i]] b[[i]])
  | .base t' => match t' with
    | .nats
    | .flts => Tm.cst2 (.arithOp op) a b
private def linOpDevec [t: BiArraysC BiLin α β γ](op: AddOp)
  (a: Tm Γ α)(b: Tm Γ β): Tm Γ γ :=
   match t.t with
  | .array n t' =>
      have: BiArraysC BiLin _ _ _ := ⟨t'⟩
      for' i => (linOpDevec op a[[i]] b[[i]])
  | .base t' => match t' with
    | .lins => Tm.cst2 (.linOp op) a b
private def linScaleDevec [t: BiArrayC BiLF α β γ](op: MulOp)
  (a: Tm Γ α)(b: Tm Γ β): Tm Γ γ :=
  let go {α' β' γ'}[t: BiLFC α' β' γ'](a: Tm Γ α')(b: Tm Γ β'): Tm Γ γ' :=
    match t.t with
    | .lf => (Tm.cst2 (.linScale op) a b)
  match t.t with
  | .array n t' =>
      have: BiLFC _ _ _ := ⟨t'⟩
      for' i => (go a[[i]] b[[i]])
  | .base t' =>
      have: BiLFC _ _ _ := ⟨t'⟩
      go a b
private def Const2.devec (a: Tm VPar α)(b: Tm VPar β): Const2 α β γ → Tm VPar γ
| arithOp op => op.devec a b
| linOp op => linOpDevec op a b
| linScale op => linScaleDevec op a b
| .addi => Tm.cst2 (.addi) a b
| .eqi => a ==' b
| .lt => a <' b
| .maxf => Max.max a b
| .get  => a[[b]]
| .tup  => (a,, b)
| .app  => a @@ b
| .cons => a.cons b
| .append => a.append b
| .mapL => a.map b
| .aFoldL => Tm.cst2 .aFoldL a b
| .aFoldA => Tm.cst2 .aFoldA a b

def Tm.devectorize: Tm VPar α → Tm VPar α
| .err => .err
| .cst0 const0 => .cst0 const0
| .cst1 const1 t => .cst1 const1 t.devectorize
| .cst2 const2 a b => const2.devec a.devectorize b.devectorize
| .abs f => fun'v x => (f x).devectorize
| .bld a => for'v idx => (a idx).devectorize
| .ite cond a b => if' cond.devectorize then a.devectorize else b.devectorize
| .var v => .var v
| .bnd rest l => let'v v := rest.devectorize; (l v).devectorize

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
