import Polara.Syntax.Index
import Polara.Optimizations.ToAinf

open Ty Tm Const0 Const1 Const2

------------------------------------------------------------------------------------------
-- fission & common subexpression elimination (AINF)
------------------------------------------------------------------------------------------

-- boolean equality ----------------------------
def Prim.beq : Prim α → Prim α → Bool
  | .err, .err => true
  | .var i, .var j => i==j
  | .abs _i f, .abs _j e => f==e
  | .bld _i f, .bld _j e => f==e
  | .ite a₀ b₀ c₀, .ite a₁ b₁ c₁ => a₀==a₁ && b₀==b₁ && c₀==c₁
  | .cst0 k₀, .cst0 k₁ => k₀==k₁
  | .cst1 (α₁:=α₀) k₀ a₀,
    .cst1 (α₁:=α₁) k₁ a₁ =>
      if hα:α₀=α₁ then
        hα▸k₀==k₁ && hα▸a₀==a₁
      else false
  | .cst2 (α₁:=α₀) (α₂:=β₀) k₀ a₀ b₀,
    .cst2 (α₁:=α₁) (α₂:=β₁) k₁ a₁ b₁ =>
      if h: α₀=α₁ ∧ β₀=β₁ then let ⟨ hα, hβ ⟩ := h
        hα▸hβ▸k₀==k₁ && hα▸a₀==a₁ && hβ▸b₀==b₁
      else false
  | _, _ => false
def AINF.beq : AINF α → AINF α → Bool
  | ([], i), ([], j) => i==j
  | (⟨⟨β, _⟩, _, p⟩ :: f, _), (⟨⟨γ, _⟩, _, p'⟩ :: f', _) =>
    if h:β=γ then p.beq (h▸p') && f.beq f' else false
  | _, _ => false

instance : BEq (Prim x) where beq a b := Prim.beq a b

-- renaming -----------------------------------
def Ren := ListMap Var Var

def Var.rename : Ren → Var α → Var α
  | [],          a => a
  | ⟨β,b,v⟩::ys, a => if h: β=α then if h▸ b==a then h▸ v
                      else rename ys a else rename ys a
def VPar.rename (r: Ren): VPar α → VPar α
  | VPar.v x => .v (x.rename r)
  | VPar.p x => .p x

def EnvPart.rename (r: Ren): EnvPart → EnvPart
| func α p     => func α p
| forc n p     => forc n p
| itec i true  => itec (i.rename r) true
| itec i false => itec (i.rename r) false

def Env.rename (r: Ren)(env: Env): Env :=
  env.map (EnvPart.rename r)

def Prim.rename (r: Ren): Prim α → Prim α
  | .cst0 k => .cst0 k
  | .cst1 k a => .cst1 k (a.rename r)
  | .cst2 k a b => .cst2 k (a.rename r) (b.rename r)
  | .err       => .err
  | .var x     => .var x
  | .abs i e   => .abs i (e.rename r)
  | .ite a b c => .ite (a.rename r) (b.rename r) (c.rename r)
  | .bld i f => .bld i (f.rename r)
  | .ref v => .ref (v.rename r)
  | .bndRef re v => .bndRef (re.rename r) (v.rename r)

def Bnd.rename (r: Ren): Bnd → Bnd
| ⟨⟨_,i⟩, env, prim⟩ => ⟨⟨_, i⟩, env.rename r, prim.rename r⟩

def AINF.rename (r: Ren): AINF α → AINF α
| (bnds, ret) => (bnds.map (Bnd.rename r), ret.rename r)
-----------------------------------------------

-- Reverse AiNF variable bindigs (like AINF.bnd) in reverse order
def RAINF := ListMap Prim (fun α => Var α × Env)

-- Trilean Left Right Middle
inductive Tern where | L | R | M

-- intersection of two environments
def Env.or (Γ: Env) (Δ: Env) (t: Tern): Option Env := match Γ, Δ with
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
def RAINF.upgrade : RAINF → Var b → Env → Option RAINF
  | [],              _, _ => return []
  | ⟨γ,k,(v,Γ)⟩::ys, i, Δ =>
    if h: γ=b then if h▸ v==i
    -- variable found
    then return ⟨γ,k,(v, <- Env.or Γ Δ .M)⟩ :: (<- RAINF.upgrade ys i Δ)
    -- variable not found
    else return ⟨γ,k,(v,Γ)⟩                 :: (<- RAINF.upgrade ys i Δ)
    else return ⟨γ,k,(v,Γ)⟩                 :: (<- RAINF.upgrade ys i Δ)

-- Renaming and RAINF to be initallized with []
def AINF.cse' (r: Ren) (σ: RAINF): AINF α → (RAINF × VPar α)
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

def RAINF.merge (rainf: RAINF) (v: VPar α): AINF α :=
  rainf.foldl (λ (acc, ret) ⟨_,x,(v,Γ)⟩ => (⟨⟨_,v⟩,Γ,x⟩ :: acc, ret)) ([], v)

def AINF.cse (a: AINF α): AINF α :=
  let (rainf, v) := a.cse' [] []
  rainf.merge v

-- invers of AINF.merge
def AINF.list: AINF α → RAINF × VPar α :=
  λ
  | ([],i)       => ([], i)
  | (⟨⟨β, v⟩, Γ, prim⟩ :: rest, ret) => AINF.list (rest, ret)|>.map (⟨β ,prim, (v, Γ)⟩ :: ·) id
  |>.map List.reverse id
