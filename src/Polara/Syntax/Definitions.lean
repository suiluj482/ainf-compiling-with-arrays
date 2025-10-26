import Polara.Utils.All
import Std

-- Type
inductive Ty
| nat : Ty                  -- natural number
| idx : Pos → Ty            -- index
| flt : Ty                  -- float
| lin : Ty                  -- linear (aD)
| arrow : Ty → Ty → Ty      -- function
| product : Ty → Ty → Ty    -- tupple
| array : Pos → Ty → Ty     -- array
| list: Ty → Ty             -- list
| unit: Ty
deriving DecidableEq, Inhabited, Hashable
open Ty
infixr : 80 " ~> " => Ty.arrow
infixr : 70 " ×× " => Ty.product

-- literals
inductive Const0 : Ty → Type
| litn : Nat → Const0 nat           -- natural number
| litf : Float → Const0 flt         -- float
| litlZ : Const0 lin                -- lin 0
| liti {n: Pos}: Fin n → Const0 (idx n) -- index
| litu : Const0 unit                -- unit
| litlE : Const0 (list α)       -- empty list []
deriving BEq
open Const0

-- unary functions
inductive Const1 : Ty → Ty → Type
| exp  : Const1 flt flt         -- exponentation
| sqrt : Const1 flt flt         -- square root
| log  : Const1 flt flt         -- log
| normCdf : Const1 flt flt      -- normal cumulative distribution function
| fst : Const1 (α ×× β) α       -- first of tupple
| snd : Const1 (α ×× β) β       -- second of tupple
| sumf : Const1 (array n flt) flt    -- sum of array
| suml : Const1 (array n lin) lin
| i2n: Const1 (idx n) nat     -- indices -> nat
| n2f  : Const1 nat flt         -- nat -> float
| arr2list : Const1 (array n α) (list α) -- array to list
deriving BEq
open Const1

def BiOpT := Ty → Ty → Ty → Type

inductive BiArith: BiOpT where
| nats: BiArith nat nat nat
| flts: BiArith flt flt flt
deriving BEq, Repr, DecidableEq
class BiArithC (α β: Ty)(γ: outParam Ty) where
  t: BiArith α β γ
deriving BEq, Repr, DecidableEq
@[default_instance] instance: BiArithC nat nat nat := ⟨BiArith.nats⟩
@[default_instance] instance: BiArithC flt flt flt := ⟨.flts⟩

inductive BiLin: BiOpT where
| lins: BiLin lin lin lin
deriving BEq, Repr, DecidableEq
class BiLinC (α β: Ty)(γ: outParam Ty) where
  t: BiLin α β γ
deriving BEq, Repr, DecidableEq
@[default_instance] instance: BiLinC lin lin lin := ⟨.lins⟩

inductive BiLF: BiOpT where
| lf: BiLF lin flt lin
deriving BEq, Repr, DecidableEq
class BiLFC (α β: Ty)(γ: outParam Ty) where
  t: BiLF α β γ
deriving BEq, Repr, DecidableEq
@[default_instance] instance: BiLFC lin flt lin := ⟨.lf⟩

class abbrev BEqRepr (α: Type u) := BEq α, Repr α
macro "∀3BR" t:term : term => `(∀ α' β' γ', BEqRepr ($t α' β' γ'))

inductive BiArrays (T: BiOpT)[∀3BR T]: BiOpT
| base: T α β γ → BiArrays T α β γ
| array (n: Pos): BiArrays T α β γ → BiArrays T (array n α) (array n β) (array n γ)
deriving BEq, Repr
class BiArraysC (T: BiOpT)[∀3BR T](α β: Ty)(γ: outParam Ty) where
  t: BiArrays T α β γ
deriving BEq, Repr
@[default_instance] instance [∀3BR T][b: BiArraysC T α β γ]:
  BiArraysC T (array n α) (array n β) (array n γ) := ⟨BiArrays.array n b.t⟩
@[default_instance] instance [b: BiArithC α β γ]: BiArraysC BiArith α β γ := ⟨.base b.t⟩
@[default_instance] instance [b: BiLinC α β γ]: BiArraysC BiLin α β γ := ⟨.base b.t⟩

inductive BiArray (T: BiOpT)[∀3BR T]: BiOpT
| base: T α β γ → BiArray T α β γ
| array (n: Pos): T α β γ → BiArray T (array n α) (array n β) (array n γ)
deriving BEq, Repr
class BiArrayC (T: BiOpT)[∀3BR T](α β: Ty)(γ: outParam Ty) where
  t: BiArray T α β γ
deriving BEq, Repr
@[default_instance] instance [b: BiLFC α β γ]: BiArrayC BiLF α β γ := ⟨.base b.t⟩
@[default_instance] instance [b: BiLFC α β γ]:
  BiArrayC BiLF (array n α) (array n β) (array n γ) := ⟨.array n b.t⟩

def BiArray.toBiArrays[∀3BR T]: BiArray T α β γ → BiArrays T α β γ
| .base t => BiArrays.base t
| .array n t => BiArrays.array n (BiArrays.base t)

inductive ArithOp: Type
| add: ArithOp
| sub: ArithOp
| mul: ArithOp
| div: ArithOp
deriving BEq, Repr

inductive AddOp
| add | sub
deriving BEq, Repr
def AddOp.toArith: AddOp → ArithOp
| .add => ArithOp.add
| .sub => ArithOp.sub

inductive MulOp
| mul | div
deriving BEq, Repr
def MulOp.toArith: MulOp → ArithOp
| .mul => ArithOp.mul
| .div => ArithOp.div

-- binary functions
inductive Const2 : Ty → Ty → Ty → Type
| arithOp [type: BiArraysC BiArith α β γ] (op: ArithOp): Const2 α β γ
| linOp [type: BiArraysC BiLin α β γ] (op: AddOp): Const2 α β γ
| linScale [type: BiArrayC BiLF α β γ] (op: MulOp): Const2 α β γ
| addi: Const2 (idx n) (idx m) (idx (n.addMinOne m))
| eqi: Const2 (idx n) (idx n) nat
| maxf : Const2 flt flt flt
| lt : Const2 flt flt nat                           -- lower than
| get : Const2 (array n α) (idx n) α          -- array access
| tup : Const2 α β (α ×× β)                   -- tupple constructor
| app : Const2 (α~>β) α β                     -- function application

| cons: Const2 α (list α) (list α)
| append: Const2 (list α) (list α) (list α)
| zipL: Const2 (list α) (list β) (list (α××β))
| mapL: Const2 (list α) (α~>β) (list β)
| foldL: Const2 (list α) ((α ~> β ~> β) ×× β) β -- fold list with assosiativ function
| foldA: Const2  (array n α) ((α ~> β ~> β) ×× β) β -- fold array with associativ function
deriving BEq
open Const2

-- Variable symbols: α is Polara Type of Variable
inductive Var : Ty → Type
| mk : Nat → Var α
deriving DecidableEq, Inhabited, Hashable
-- Parameter symbols: argument overall functions, loop index
inductive Par : Ty → Type
| mk : Nat → Par α
deriving DecidableEq, Inhabited, Hashable
-- Var or Par symbols
inductive VPar α
| v : Var α → VPar α
| p : Par α → VPar α
deriving DecidableEq, Inhabited, Hashable

def VPar.var?: VPar α → Option (Var α)
| .v var => var
| .p _ => none
def VPar.par?: VPar α → Option (Par α)
| .v _ => none
| .p par => par

------------------------------------------------------------------------------------------
-- Polara
------------------------------------------------------------------------------------------

-- Polara Term:
--    Γ is Domain of Variables with Ty z.B. VPar having number as Name α as ty
--      Γ α is a Variable Symbol of a Variable of Ty α z.B. Var 0 ~ x0
--    α is Ty of Term
inductive Tm (Γ: Ty → Type): Ty → Type
| err : Tm Γ α -- error
| cst0 : Const0 α → Tm Γ α -- cst0 takes no arguments
| cst1 : Const1 α₁ α → Tm Γ α₁ → Tm Γ α -- cst1 takes one argument
| cst2 : Const2 α₁ α₂ α → Tm Γ α₁ → Tm Γ α₂ → Tm Γ α -- cst2 takes two arguments
| abs : (Γ α → Tm Γ β) → Tm Γ (α ~> β)          -- abstraktion / lambda function
| bld : (Γ (idx n) → Tm Γ α) → Tm Γ (array n α) -- build / array constructor
| ite : Tm Γ nat → Tm Γ β → Tm Γ β → Tm Γ β       -- if (·: nat neq 0) then · else ·
| var : Γ α → Tm Γ α                              -- variable of type α
| bnd : Tm Γ α → (Γ α → Tm Γ β) → Tm Γ β        -- bind tm to variable / let
-- | litA {n: Pos}: (Fin n → Tm Γ α) → Tm Γ (array n α)
open Tm

abbrev Term: Ty → Type := Tm VPar

instance : Inhabited (Tm Γ α) := ⟨Tm.err⟩

------------------------------------------------------------------------------------------
-- AINF
------------------------------------------------------------------------------------------

inductive EnvPart : Type -- envPart modeling control flow
| func : (α:Ty) → Par α → EnvPart         -- function control flow
| forc : (n:Pos) → Par (idx n) → EnvPart  -- for
| itec : VPar nat → Bool → EnvPart        -- if then else
deriving DecidableEq, Hashable
abbrev Env := List EnvPart

-- primitive operations (could maybe be unified with Tm)
inductive Prim : Ty → Type
| cst0 : Const0 α → Prim α
| cst1 : Const1 α₁ α → VPar α₁ → Prim α
| cst2 : Const2 α₁ α₂ α → VPar α₁ → VPar α₂ → Prim α
| err : Prim α
| var : VPar α → Prim α
| abs : Par α → VPar β → Prim (α ~> β)
| ite : VPar nat → VPar α → VPar α → Prim α
| bld : Par (idx n) → VPar α → Prim (array n α)
deriving BEq
instance: Inhabited (Prim α) := ⟨Prim.err⟩

def Prim.vpars: Prim α → List (Sigma VPar)
| cst0 _ => []
| cst1 _ v => [⟨_,v⟩]
| cst2 _ v1 v2 => [⟨_,v1⟩, ⟨_,v2⟩]
| err => []
| var v => [⟨_,v⟩]
| abs _ v => [⟨_,v⟩]
| ite v1 v2 v3 => [⟨_,v1⟩, ⟨_,v2⟩, ⟨_,v3⟩]
| bld _ v => [⟨_,v⟩]

abbrev Bnd := DListMap.eT (Sigma Var) (λ ⟨α,_⟩ => Env × Prim α)
abbrev Bnds := DListMap (Sigma Var) (λ ⟨α,_⟩ => Env × Prim α)
abbrev AINF α := Bnds × (Var α) -- return variable

instance: BEq Bnd := ⟨λ ⟨⟨α,v⟩,e,p⟩ ⟨⟨α',v'⟩,e',p'⟩ =>
    if t: α=α' then
      v == t▸v' && e == e' && p == t▸p'
    else false
  ⟩

def Prim.vars (p: Prim α): List (Sigma Var) :=
  p.vpars.filterMap (λ ⟨_, v⟩ => return ⟨_, ←v.var?⟩) |>.toSet
def Prim.pars (p: Prim α): List (Sigma Par) :=
  p.vpars.filterMap (λ ⟨_, v⟩ => return ⟨_, ←v.par?⟩) |>.toSet
def EnvPar.vpar?: EnvPart → Option (Sigma VPar)
| .itec cond _ => some ⟨_,cond⟩
| .forc _ _ => none
| .func _ _ => none
def Env.vpars: Env → List (Sigma VPar)
| env => env.filterMap EnvPar.vpar? |>.toSet
def Env.vars: Env → List (Sigma Var)
| env => env.vpars.filterMap (λ ⟨_,v⟩ => return ⟨_,←v.var?⟩) |>.toSet
def Bnd.vpars: Bnd → List (Sigma VPar)
| ⟨⟨_,_⟩,env,prim⟩ => env.vpars.addSets prim.vpars

def filterVars (l: List (Sigma VPar)): List (Sigma Var) :=
  l.filterMap (λ ⟨_, v⟩ => return ⟨_, ←v.var?⟩)
def filterPars (l: List (Sigma VPar)): List (Sigma Par) :=
  l.filterMap (λ ⟨_, v⟩ => return ⟨_, ←v.par?⟩)
def Bnd.var: Bnd → Sigma Var := (λ ⟨v,_,_⟩ => v)
def Bnd.vars := filterVars ∘ Bnd.vpars
def Bnd.pars := filterPars ∘ Bnd.vpars
def Var.num: Var α → Nat | ⟨n⟩ => n
def Par.num: Par α → Nat | ⟨n⟩ => n
def VPar.num: VPar α → Nat
| .v ⟨n⟩ | .p ⟨n⟩ => n

-- HashMap
-- + faster lookup
-- - no order (renaming harder)
deriving instance Hashable for Var
deriving instance Hashable for Par
deriving instance Hashable for VPar
abbrev BndsH := Std.DHashMap (Sigma Var) (λ ⟨α,_⟩ => Env × Prim α)
abbrev AINFH α := BndsH × Var α

def AINF.toHashMap: AINF α → AINFH α
| (bnds, ret) => (
    Std.DHashMap.ofList bnds,
    ret
  )
def AINFH.toList: AINFH α → AINF α
| (bnds, ret) => (
  bnds.topologicalSort (λ _ ⟨_, p⟩ => p.vars),
  ret
)
