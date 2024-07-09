import Polara.Syntax

open Ty Tm Const0 Const1 Const2

------------------------------------------------------------------------------------------
-- fission & common subexpression elimination (AINF)
------------------------------------------------------------------------------------------

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

@[reducible] def Counter := ReaderM Nat

def AINF.smart_bnd : Env → Prim α → (VPar α → Counter (AINF β)) → Counter (AINF β)
  | _, .var x => fun k i => k x i
  | Γ, p => fun k i =>
    let x := Var.mk i
    bnd Γ x p (k (.v x) (i+1))

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

def RAINF := ListMap Prim (fun α => Var α × Env)

instance : BEq (Prim x) where beq a b := Prim.beq a b

inductive Tern where | L | R | M

def Env.or (Γ: Env) (Δ: Env): Tern → Option Env := fun t => match Γ, Δ with
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
  | itec Γ _ _, Δ => match t with
    | .L => Γ.or Δ .L
    | .M => Γ.or Δ .L
    | .R => none
  | Γ, itec Δ _ _ => match t with
    | .L => none
    | .M => Γ.or Δ .R
    | .R => Γ.or Δ .R
  | _,          _          => none

def RAINF.upgrade : RAINF → Var b → Env → Option RAINF
  | [],              _, _ => return []
  | ⟨γ,k,(v,Γ)⟩::ys, i, Δ =>
    if h: γ=b then if h▸ v==i
    then return ⟨γ,k,(v, <- Env.or Γ Δ .M)⟩ :: (<- RAINF.upgrade ys i Δ)
    else return ⟨γ,k,(v,Γ)⟩                 :: (<- RAINF.upgrade ys i Δ)
    else return ⟨γ,k,(v,Γ)⟩                 :: (<- RAINF.upgrade ys i Δ)

def AINF.cse' : Ren → RAINF → AINF α → (RAINF × VPar α)
  | r,σ, ret i       => (σ, i.rename r)
  | r,σ, bnd Γ i v e =>
    let Γ' := Γ.rename r
    let v' := v.rename r

    let tmp := do
      let (i',_) <- σ.lookup v'
      let σ'     <- σ.upgrade i' Γ
      return (i',σ')

    match tmp with -- put (Γ,i,v) into renaming OR naming
    | none         => cse' r (⟨_,v',(i,Γ')⟩::σ) e
    | some (i',σ') => cse' (⟨_,i,i'⟩::r)     σ' e

-- a RAINF is a chain of let-bindings, a VPar is a final variable
-- an AINF is a chain of let-bindings and a final variable
def merge: RAINF → VPar α → AINF α
  | [],              y => .ret y
  | ⟨_,x,(v,Γ)⟩::ys, y => .bnd Γ v x (merge ys y)

def AINF.cse : Ren → RAINF → AINF α → AINF α
  | r, σ, a => let (b, c) := a.cse' r σ; merge b.reverse c
