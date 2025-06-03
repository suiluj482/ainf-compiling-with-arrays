import Polara.Syntax.Index

open Ty Tm Const0 Const1 Const2

------------------------------------------------------------------------------------------
-- fission & common subexpression elimination (AINF)
------------------------------------------------------------------------------------------

-- toAINF
@[reducible] def Counter := ReaderM Nat

-- no new variable for .var
-- Counter monade for vars numbers begining with 0
def AINF.smart_bnd : Env → Prim α → (VPar α → Counter (AINF β)) → Counter (AINF β)
  | _, .var x, k => fun i => k x i
  | Γ, p     , k => fun i =>
    let x := Var.mk i
    bnd Γ x p (k (.v x) (i+1)) -- +1 counter

def Tm.toAINF (e : Tm VPar α) : AINF α :=
  (go 0 .nil e fun v _i => .ret v) 0
  where go {α β} (j : Nat) (Γ : Env) (e : Tm VPar α)
           (reti : VPar α → Counter (AINF β)): Counter (AINF β) := match e with
  | err => .smart_bnd Γ .err reti
  | var x => .smart_bnd Γ (.var x) reti
  | cst0 c => .smart_bnd Γ (.cst0 c) reti
  | cst1 c e₁ =>
    go j Γ e₁ fun v₁ =>
    .smart_bnd Γ (.cst1 c v₁) reti
  | cst2 c e₁ e₂ =>
    go j Γ e₁ fun v₁ =>
    go j Γ e₂ fun v₂ =>
    .smart_bnd Γ (.cst2 c v₁ v₂) reti
  | abs e =>
    let xx := Par.mk j
    go (j+1) (.func Γ _ xx) (e (.p xx)) fun v =>
    .smart_bnd Γ (.abs xx v) reti
  | bld (n:=n) e =>
    let xx : Par (idx n) := Par.mk j
    go (j+1) (.forc Γ n xx) (e (.p xx)) fun v =>
    .smart_bnd Γ (.bld xx v) reti
  | ite e₁ e₂ e₃ =>
    go j Γ e₁ fun v₁ =>
    go j (.itec Γ v₁ true ) e₂ fun v₂ =>
    go j (.itec Γ v₁ false) e₃ fun v₃ =>
    .smart_bnd Γ (.ite v₁ v₂ v₃) reti
  | bnd e f =>
    go j Γ e fun v =>
    go j Γ (f v) reti

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
  | .ret i, .ret j => i==j
  | .bnd (α:=β) _Γ _i v f, .bnd (α:=γ) _Δ _j w e =>
    if h:β=γ then v.beq (h▸w) && f.beq e else false
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

def Env.rename (r: Ren): Env → Env
  | nil => .nil
  | func Γ α p     => func (Γ.rename r) α p
  | forc Γ n p     => forc (Γ.rename r) n p
  | itec Γ i true  => itec (Γ.rename r) (i.rename r) true
  | itec Γ i false => itec (Γ.rename r) (i.rename r) false

def Prim.rename (r: Ren): Prim α → Prim α
  | .cst0 k => .cst0 k
  | .cst1 k a => .cst1 k (a.rename r)
  | .cst2 k a b => .cst2 k (a.rename r) (b.rename r)
  | .err       => .err
  | .var x     => .var x
  | .abs i e   => .abs i (e.rename r)
  | .ite a b c => .ite (a.rename r) (b.rename r) (c.rename r)
  | .bld i f => .bld i (f.rename r)

def AINF.rename (r: Ren): AINF α → AINF α
  | .ret i       => .ret (i.rename r)
  | .bnd Γ i v e => .bnd (Γ.rename r) i (v.rename r) (e.rename r)
-----------------------------------------------

-- Reverse AiNF variable bindigs (like AINF.bnd) in reverse order
def RAINF := ListMap Prim (fun α => Var α × Env)

-- Trilean Left Right Middle
inductive Tern where | L | R | M

-- intersection of two environments
def Env.or (Γ: Env) (Δ: Env) (t: Tern): Option Env := match Γ, Δ with
  -- keep if identical
  | nil,        nil        => return .nil
  | func Γ α p, func Δ β q =>
    if h: α=β then if h▸ p==q then return func (<- Γ.or Δ t) α p else none else none
  | forc Γ n p, forc Δ m q =>
    if h: n=m then if h▸ p==q then return forc (<- Γ.or Δ t) n p else none else none
  | itec Γ i b, itec Δ j d =>
    if i==j then
      if b==d
      then return itec (<- Γ.or Δ t) i b  -- keep
      else return      (<- Γ.or Δ t)      -- (i=T||i=F) <-> T
    else none
  -- keep itec if on Trilean side or Middle
  | itec Γ _ _, Δ => match t with
    | .L => Γ.or Δ .L
    | .M => Γ.or Δ .L
    | .R => none
  | Γ, itec Δ _ _ => match t with
    | .L => none
    | .M => Γ.or Δ .R
    | .R => Γ.or Δ .R
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
  | ret v       => (σ, v.rename r)
  | bnd Γ v prim rest =>
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
    | none         => cse' r              (⟨_,prim',(v,Γ')⟩::σ) rest
    -- identical variable RAINF found => rename to it, update RAINF with new env
    | some (v',σ') => cse' (⟨_,v,v'⟩::r)  σ'                    rest

def RAINF.merge (rainf: RAINF) (v: VPar α): AINF α :=
  rainf.foldl (λ acc ⟨_,x,(v,Γ)⟩ => .bnd Γ v x acc) (.ret v)

def AINF.cse (a: AINF α): AINF α :=
  let (rainf, v) := a.cse' [] []
  rainf.merge v

-- invers of AINF.merge
def AINF.list: AINF α → RAINF × VPar α :=
  λ
  | .ret i       => ([], i)
  | .bnd (α:=β) Γ v prim rest => rest.list.map (⟨β ,prim, (v, Γ)⟩ :: ·) id
  |>.map List.reverse id
