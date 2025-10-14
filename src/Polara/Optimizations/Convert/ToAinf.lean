import Polara.Syntax.All


@[reducible] def Counter := ReaderM Nat

-- smart bnd prevents new variables for Prim.var
def AINF.smart_bnd (env: Env) (p: Prim α) (k: Var α → Counter (AINF β)): Counter (AINF β) :=
  match env, p with
  | _, .var (.v x) => k x
  | env, p    => λ counter =>
    let x := Var.mk counter
    ((k x) (counter+1)).map (⟨⟨_,x⟩, env, p⟩ ::·) id -- +1 counter

def Tm.toAINF' {α β} (j: Nat)(env : Env) (e : Tm VPar α)
           (reti : Var α → Counter (AINF β)): Counter (AINF β) := match e with
  | err => AINF.smart_bnd env .err reti
  | var x => AINF.smart_bnd env (.var x) reti
  | cst0 c => AINF.smart_bnd env (.cst0 c) reti
  | cst1 c e₁ =>
    toAINF' j env e₁ fun v₁ =>
    AINF.smart_bnd env (.cst1 c (.v v₁)) reti
  | cst2 c e₁ e₂ =>
    toAINF' j env e₁ fun v₁ =>
    toAINF' j env e₂ fun v₂ =>
    AINF.smart_bnd env (.cst2 c (.v v₁) (.v v₂)) reti
  | abs e =>
    let xx := Par.mk j
    toAINF' (j+1) (.func _ xx :: env) (e (.p xx)) fun v =>
    AINF.smart_bnd env (.abs xx (.v v)) reti
  | bld (n:=n) e =>
    let xx := Par.mk j
    toAINF' (j+1) (.forc n xx :: env) (e (.p xx)) fun v =>
    AINF.smart_bnd env (.bld xx (.v v)) reti
  | ite e₁ e₂ e₃ =>
    toAINF' j env e₁ fun v₁ =>
    toAINF' j (.itec (.v v₁) true :: env) e₂ fun v₂ =>
    toAINF' j (.itec (.v v₁) false :: env) e₃ fun v₃ =>
    AINF.smart_bnd env (.ite (.v v₁) (.v v₂) (.v v₃)) reti
  | bnd e f =>
    toAINF' j env e fun v =>
    toAINF' j env (f (.v v)) reti

def Tm.toAINFC (e: Tm VPar α): Counter (AINF α) :=
  (toAINF' 0 .nil e fun v => pure ([], v))

def Tm.toAINF (e : Tm VPar α) : AINF α :=
  e.toAINFC 0


-- -- todo: reset par num on new row?
-- def AINF.smart_bnd (env: Env) (p: Prim α) (k: VPar α → VParM (AINF β)): VParM (AINF β) :=
--   match env, p with
--   | _, .var x => k x
--   | env, p    => do
--     let x := (←VParM.var) α
--     return (←(k (.v x))).map (⟨⟨_,x⟩, env, p⟩ ::·) id -- +1 counter

-- def Tm.toAINF' {α β} (env : Env) (e : Tm VPar α)
--            (reti : VPar α → VParM (AINF β)): VParM (AINF β) := match e with
--   | err => AINF.smart_bnd env .err reti
--   | var x => AINF.smart_bnd env (.var x) reti
--   | cst0 c => AINF.smart_bnd env (.cst0 c) reti
--   | cst1 c e₁ =>
--     toAINF' env e₁ fun v₁ =>
--     AINF.smart_bnd env (.cst1 c v₁) reti
--   | cst2 c e₁ e₂ =>
--     toAINF' env e₁ fun v₁ =>
--     toAINF' env e₂ fun v₂ =>
--     AINF.smart_bnd env (.cst2 c v₁ v₂) reti
--   | abs e => do
--     let xx := (←VParM.par) _
--     toAINF' (.func _ xx :: env) (e (.p xx)) fun v =>
--     AINF.smart_bnd env (.abs xx v) reti
--   | bld (n:=n) e => do
--     let xx := (←VParM.par) (.idx n)
--     toAINF' (.forc n xx :: env) (e (.p xx)) fun v =>
--     AINF.smart_bnd env (.bld xx v) reti
--   | ite e₁ e₂ e₃ =>
--     toAINF' env e₁ fun v₁ =>
--     toAINF' (.itec v₁ true :: env) e₂ fun v₂ =>
--     toAINF' (.itec v₁ false :: env) e₃ fun v₃ =>
--     AINF.smart_bnd env (.ite v₁ v₂ v₃) reti
--   | bnd e f =>
--     toAINF' env e fun v =>
--     toAINF' env (f v) reti

-- def Tm.toAINFM (e: Tm VPar α): VParM (AINF α) :=
--   (toAINF' .nil e fun v => pure ([], v))

-- def Tm.toAINFMEV (env: Env)(v: Var α)(t: Tm VPar α): VParM Bnds :=
--   do
--     let (bnds, ret) ← (toAINF' .nil t fun v => pure ([], v))
--     return bnds.cons ⟨⟨_,v⟩, env, .var ret⟩

-- def Tm.toAINF (e : Tm VPar α) : AINF α :=
--   e.toAINFM ⟨(0,0)⟩ |>.fst

-- ---

-- abbrev BndTm := DListMap.eT (Sigma Var) (λ ⟨α,_⟩ => Env × Tm VPar α)

-- def AINF.mapBndTm (f: (α: Ty) → Env → Prim α → Option (Env × Tm VPar α))(a: AINF α): AINF α := match a with
-- | (bnds, v) => (
--     bnds.flatMapM (λ (bnd: Bnd) => match bnd with
--       | ⟨⟨α,v⟩, env, prim⟩ =>
--         match (f α env prim) with
--         | none => pure [bnd]
--         | some (env', tm') => tm'.toAINFMEV env' v
--     ) |>.freshAINFVars a,
--     v
--   )

-- def AINF.mapBndTmF (t: Ty → Ty)(f: (α: Ty) → Env → Prim α → Env × Tm VPar (t α))(a: AINF α): AINF (t α) := match a with
-- | (bnds, v) => (
--     bnds.flatMapM (λ (bnd: Bnd) => match bnd with
--       | ⟨⟨α,v⟩, env, prim⟩ =>
--         let (env', tm') := (f α env prim)
--         tm'.toAINFMEV env' (v.changeTypeF t)
--     ) |>.freshAINFVars a,
--     v.changeTypeF t
--   )
