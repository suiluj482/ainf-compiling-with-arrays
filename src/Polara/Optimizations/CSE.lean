import Polara.Syntax.All

open Ty Tm Const0 Const1 Const2

------------------------------------------------------------------------------------------
-- fission & common subexpression elimination (AINF)
------------------------------------------------------------------------------------------

-- renaming -----------------------------------
private def Ren := ListMap Var Var

private def Var.rename : Ren → Var α → Var α
  | [],          a => a
  | ⟨β,b,v⟩::ys, a => if h: β=α then if h▸ b==a then h▸ v
                      else rename ys a else rename ys a
private def VPar.rename (r: Ren): VPar α → VPar α
  | VPar.v x => .v (x.rename r)
  | VPar.p x => .p x

private def EnvPart.rename (r: Ren): EnvPart → EnvPart
| func α p     => func α p
| forc n p     => forc n p
| itec i true  => itec (i.rename r) true
| itec i false => itec (i.rename r) false

private def Env.rename (r: Ren)(env: Env): Env :=
  env.map (EnvPart.rename r)

private def Prim.rename (r: Ren): Prim α → Prim α
  | .cst0 k => .cst0 k
  | .cst1 k a => .cst1 k (a.rename r)
  | .cst2 k a b => .cst2 k (a.rename r) (b.rename r)
  | .err       => .err
  | .var x     => .var x
  | .abs i e   => .abs i (e.rename r)
  | .ite a b c => .ite (a.rename r) (b.rename r) (c.rename r)
  | .bld i f => .bld i (f.rename r)
private def Bnd.rename (r: Ren): Bnd → Bnd
| ⟨⟨_,i⟩, env, prim⟩ => ⟨⟨_, i⟩, env.rename r, prim.rename r⟩

private def AINF.rename (r: Ren): AINF α → AINF α
| (bnds, ret) => (bnds.map (Bnd.rename r), ret.rename r)
-----------------------------------------------

-- Reverse AiNF variable bindigs (like AINF.bnd) in reverse order
private def RAINF := ListMap Prim (fun α => Var α × Env)

-- Trilean Left Right Middle
inductive Tern where | L | R | M

-- intersection of two environments
private def Env.or (Γ: Env) (Δ: Env) (t: Tern): Option Env := match Γ, Δ with
  -- keep if identical
  | [],         []        => return .nil
  | .func α p :: Γ, .func β q :: Δ =>
    if h: α=β then if h▸ p==q then return .func α p :: (<- Env.or Γ Δ t) else none else none
  | .forc n p :: Γ, .forc m q :: Δ =>
    if h: n=m then if h▸ p==q then return .forc n p :: (<- Env.or Γ Δ t) else none else none
  | .itec i b :: Γ, .itec j d :: Δ =>
    if i==j then
      if b==d
      then return .itec i b :: (<- Env.or Γ Δ t)  -- keep
      else return      (<- Env.or Γ Δ t)      -- (i=T||i=F) <-> T
    else none
  -- keep itec if on Trilean side or Middle
  | .itec _ _ :: Γ, Δ => match t with
    | .L => Env.or Γ Δ .L
    | .M => Env.or Γ Δ .L
    | .R => none
  | Γ, .itec _ _ :: Δ => match t with
    | .L => none
    | .M => Env.or Γ Δ .R
    | .R => Env.or Γ Δ .R
  -- else none
  | _,          _          => none

-- lookup variable and or its environments with the given environment
private def RAINF.upgrade : RAINF → Var b → Env → Option RAINF
  | [],              _, _ => return []
  | ⟨γ,k,(v,Γ)⟩::ys, i, Δ =>
    if h: γ=b then if h▸ v==i
    -- variable found
    then return ⟨γ,k,(v, <- Env.or Γ Δ .M)⟩ :: (<- RAINF.upgrade ys i Δ)
    -- variable not found
    else return ⟨γ,k,(v,Γ)⟩                 :: (<- RAINF.upgrade ys i Δ)
    else return ⟨γ,k,(v,Γ)⟩                 :: (<- RAINF.upgrade ys i Δ)

-- Renaming and RAINF to be initallized with []
private def AINF.cse' (r: Ren) (σ: RAINF): AINF α → (RAINF × Var α)
  | ([], v)       => (σ, v.rename r)
  | (⟨⟨_,v⟩, Γ, prim⟩ :: rest, ret) =>
    let Γ' := Γ.rename r
    let prim' := prim.rename r

    let tmp := do
      -- lookup prim in allready optimized rainf
      let (v', _Γ') <- σ.lookup prim'
      -- try to upgrade existing variable env to be usable like new variable
      let σ'        <- σ.upgrade v' Γ
      return (v',σ')

    match tmp with
    -- no identical variable in RAINF found => add new variable
    | none         => cse' r              (⟨_,prim',(v,Γ')⟩::σ) (rest, ret)
    -- identical variable RAINF found => rename to it, update RAINF with new env
    | some (v',σ') => cse' (⟨_,v,v'⟩::r)  σ'                    (rest, ret)

private def RAINF.merge (rainf: RAINF) (v: Var α): AINF α :=
  rainf.foldl (λ (acc, ret) ⟨_,x,(v,Γ)⟩ => (⟨⟨_,v⟩,Γ,x⟩ :: acc, ret)) ([], v)

def AINF.cse (a: AINF α): AINF α :=
  let (rainf, v) := a.cse' [] []
  rainf.merge v

-- invers of AINF.merge
private def AINF.list: AINF α → RAINF × Var α :=
  λ
  | ([],i)       => ([], i)
  | (⟨⟨β, v⟩, Γ, prim⟩ :: rest, ret) => AINF.list (rest, ret)|>.map (⟨β ,prim, (v, Γ)⟩ :: ·) id
  |>.map List.reverse id
