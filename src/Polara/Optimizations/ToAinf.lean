import Polara.Syntax.Index

-- todo reset par num on new row?
-- destroy tuples?

-- no new variable for .var
def AINF.smart_bnd (env: Env) (p: Prim α) (k: VPar α → VParM (AINF β)): VParM (AINF β) :=
  match env, p with
  | _, .var x => k x
  | env, p    => do
    let x := (←VParM.var) α
    return (←(k (.v x))).map (⟨⟨_,x⟩, env, p⟩ ::·) id -- +1 counter

def Tm.toAINF' {α β} (env : Env) (e : Tm VPar α)
           (reti : VPar α → VParM (AINF β)): VParM (AINF β) := match e with
  | err => AINF.smart_bnd env .err reti
  | var x => AINF.smart_bnd env (.var x) reti
  | cst0 c => AINF.smart_bnd env (.cst0 c) reti
  | cst1 c e₁ =>
    toAINF' env e₁ fun v₁ =>
    AINF.smart_bnd env (.cst1 c v₁) reti
  | cst2 c e₁ e₂ =>
    toAINF' env e₁ fun v₁ =>
    toAINF' env e₂ fun v₂ =>
    AINF.smart_bnd env (.cst2 c v₁ v₂) reti
  | abs e => do
    let xx := (←VParM.par) _
    toAINF' (.func _ xx :: env) (e (.p xx)) fun v =>
    AINF.smart_bnd env (.abs xx v) reti
  | bld (n:=n) e => do
    let xx := (←VParM.par) (.idx n)
    toAINF' (.forc n xx :: env) (e (.p xx)) fun v =>
    AINF.smart_bnd env (.bld xx v) reti
  | ite e₁ e₂ e₃ =>
    toAINF' env e₁ fun v₁ =>
    toAINF' (.itec v₁ true :: env) e₂ fun v₂ =>
    toAINF' (.itec v₁ false :: env) e₃ fun v₃ =>
    AINF.smart_bnd env (.ite v₁ v₂ v₃) reti
  | bnd e f =>
    toAINF' env e fun v =>
    toAINF' env (f v) reti
  | ref f => do
    let xr := (←VParM.var) _
    let x := (←VParM.var) _
    let t := f (.v xr) (.v x)
    AINF.smart_bnd env (.ref x) fun _ =>
    toAINF' env t reti
  | bndRef xr x =>
    toAINF' env xr fun v₁ =>
    toAINF' env x  fun v₂ =>
    AINF.smart_bnd env (.bndRef v₁ v₂) reti

def Tm.toAINFM (e: Tm VPar α): VParM (AINF α) :=
  (toAINF' .nil e fun v => pure ([], v))

def Tm.toAINFMEV (env: Env)(v: Var α)(t: Tm VPar α): VParM Bnds :=
  do
    let (bnds, ret) ← (toAINF' .nil t fun v => pure ([], v))
    return bnds.cons ⟨⟨_,v⟩, env, .var ret⟩

def Tm.toAINF (e : Tm VPar α) : AINF α :=
  e.toAINFM ⟨(0,0)⟩ |>.fst
