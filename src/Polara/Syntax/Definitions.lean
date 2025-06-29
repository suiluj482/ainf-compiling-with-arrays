import Polara.Utils.Index

-- Type
inductive Ty
  | nat : Ty                  -- natural number
  | idx : Nat → Ty            -- index
  | flt : Ty                  -- float
  | lin : Ty                  -- linear (aD)
  | arrow : Ty → Ty → Ty      -- function
  | product : Ty → Ty → Ty    -- tupple
  | array : Nat → Ty → Ty     -- array
  deriving DecidableEq, Inhabited, BEq
  open Ty
  infixr : 80 " ~> " => Ty.arrow
  infixr : 70 " ×× " => Ty.product

-- literals
inductive Const0 : Ty → Type
  | litn : Nat → Const0 nat           -- natural number
  | litf : Float → Const0 flt         -- float
  | litl : Float → Const0 lin         -- float| litf : Float → Const0 flt         -- float
  | liti : Fin (n+1) → Const0 (idx n) -- index
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
  | sumf : Const1 (array n flt) flt    -- sum of array Monoide fordern
  | suml : Const1 (array n lin) lin
  -- | mul
  | i2n  : Const1 (idx n) nat     -- indices -> nat
  | n2f  : Const1 nat flt         -- nat -> float
  deriving BEq
  open Const1

def BiOpT := Ty → Ty → Ty → Type

inductive BiArith: BiOpT where
| nats: BiArith nat nat nat
| flts: BiArith flt flt flt
deriving BEq, Repr
class BiArithC (α β: Ty)(γ: outParam Ty) where
  t: BiArith α β γ
deriving BEq, Repr
@[default_instance] instance: BiArithC nat nat nat := ⟨BiArith.nats⟩
@[default_instance] instance: BiArithC flt flt flt := ⟨.flts⟩

inductive BiLin: BiOpT where
| lins: BiLin lin lin lin
deriving BEq, Repr
class BiLinC (α β: Ty)(γ: outParam Ty) where
  t: BiLin α β γ
deriving BEq, Repr
@[default_instance] instance: BiLinC lin lin lin := ⟨.lins⟩

inductive BiLF: BiOpT where
| lf: BiLF lin flt lin
deriving BEq, Repr
class BiLFC (α β: Ty)(γ: outParam Ty) where
  t: BiLF α β γ
deriving BEq, Repr
@[default_instance] instance: BiLFC lin flt lin := ⟨.lf⟩

class abbrev BEqRepr (α: Type u) := BEq α, Repr α
macro "∀3BR" t:term : term => `(∀ α' β' γ', BEqRepr ($t α' β' γ'))

inductive BiArrays (T: BiOpT)[∀3BR T]: BiOpT
| base: T α β γ → BiArrays T α β γ
| array (n: Nat): BiArrays T α β γ → BiArrays T (array n α) (array n β) (array n γ)
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
| array (n: Nat): T α β γ → BiArray T (array n α) (array n β) (array n γ)
deriving BEq, Repr
class BiArrayC (T: BiOpT)[∀3BR T](α β: Ty)(γ: outParam Ty) where
  t: BiArray T α β γ
deriving BEq, Repr
@[default_instance] instance [b: BiLFC α β γ]: BiArrayC BiLF α β γ := ⟨.base b.t⟩
@[default_instance] instance [b: BiLFC α β γ]:
  BiArrayC BiLF (array n α) (array n β) (array n γ) := ⟨.array n b.t⟩

inductive ArithOp: Type
| add: ArithOp
| sub: ArithOp
| mul: ArithOp
| div: ArithOp
deriving BEq, Repr

inductive AddOp: Type
| add: AddOp
| sub: AddOp
deriving BEq, Repr

inductive MulOp: Type
| mul: MulOp
| div: MulOp
deriving BEq, Repr

-- binary functions
inductive Const2 : Ty → Ty → Ty → Type
  | arithOp [type: BiArraysC BiArith α β γ] (op: ArithOp): Const2 α β γ
  | linOp [type: BiArraysC BiLin α β γ] (op: AddOp): Const2 α β γ
  | linScale [type: BiArrayC BiLF α β γ] (op: MulOp): Const2 α β γ

  | addi: Const2 (idx n) (idx m) (idx (n+m))
  | maxf : Const2 flt flt flt
  | get : Const2 (array n a) (idx n) a          -- array access
  | tup : Const2 α β (α ×× β)                   -- tupple constructor
  | app : Const2 (α~>β) α β                     -- function application
-- kinda missing: zip, reduce?
  deriving BEq
  open Const2

-- Variable symbols: α is Polara Type of Variable
inductive Var : Ty → Type
  | mk : Nat → Var α
  deriving DecidableEq, BEq
-- Parameter symbols: argument overall functions, loop index
inductive Par : Ty → Type
  | mk : Nat → Par α
  deriving DecidableEq, BEq
-- Var or Par symbols
inductive VPar α
  | v : Var α → VPar α
  | p : Par α → VPar α
  deriving DecidableEq, BEq

#check VPar
#check ((VPar.v (Var.mk 0)): VPar Ty.nat)

------------------------------------------------------------------------------------------
-- Polara
------------------------------------------------------------------------------------------

-- Polara Term:
--    Γ is Domain of Variables with Ty z.B. VPar having number as Name α as ty
--      Γ α is a Variable Symbol of a Variable of Ty α z.B. Var 0 ~ x0
--    α is Ty of Term
inductive Tm (Γ: Ty → Type): Ty → Type
  | err : Tm Γ α                                            -- error
  | cst0 : Const0          α →                     Tm Γ α   -- constants
  | cst1 : Const1 α₁       α → Tm Γ α₁ →           Tm Γ α   --    incl. func. application
  | cst2 : Const2 α₁ α₂    α → Tm Γ α₁ → Tm Γ α₂ → Tm Γ α   --    because else Const2.app would be needed
  | abs : (Γ α → Tm Γ β) → Tm Γ (α ~> β)                    -- lambda, abstraktion, function definition
  | bld : (Γ (idx n) → Tm Γ α) → Tm Γ (array n α)           -- build, construct array
  | ite : Tm Γ nat → Tm Γ β → Tm Γ β → Tm Γ β               -- if (·: nat neq 0) then · else ·
  | var : Γ α → Tm Γ α                                      -- variable of type α
  | bnd : Tm Γ α → (Γ α → Tm Γ β) → Tm Γ β                  -- bind: (Γ α := term; term) the latter term can use xᵢ ~ function depending on it
  open Tm

def Term: Ty → Type := Tm VPar

#check Tm VPar Ty.nat

------------------------------------------------------------------------------------------
-- AINF
------------------------------------------------------------------------------------------

-- Environemnt, Context: list of control flow to apply to primitive
--   reverse order so Env.func (Env.forc ...) ... => forc ..., func ...
inductive Env : Type
  | nil  : Env                                --
  | func : Env → (α:Ty) → Par α → Env         -- function control flow
  | forc : Env → (n:Nat) → Par (idx n) → Env  -- for
  | itec : Env → VPar nat → Bool → Env        -- if then else
  deriving DecidableEq, Inhabited

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

-- non empty list of variable definitions with primitives in an environment
inductive AINF : Ty → Type -- Var übergeben
  | ret : VPar α → AINF α   -- VPar to be returned
  | bnd : Env → Var α → Prim α → AINF β → AINF β  -- Environemnt xᵢ := Prim; ...
    -- Beweis fordern, das Var definiert

----------
inductive EnvPart : Type                    --
  | func : (α:Ty) → Par α → EnvPart         -- function control flow
  | forc : (n:Nat) → Par (idx n) → EnvPart  -- for
  | itec : VPar nat → Bool → EnvPart        -- if then else
  deriving DecidableEq

def Env.fromList (e: List EnvPart): Env :=
  e.foldl (λ acc x => match x with
    | .func α p => Env.func acc α p
    | .forc n p => Env.forc acc n p
    | .itec cond ref => Env.itec acc cond ref
    ) Env.nil
def Env.toList: Env → List EnvPart :=
  let rec aux := (λ
  | .nil => []
  | .func acc α p => EnvPart.func α p :: aux acc
  | .forc acc n p => EnvPart.forc n p :: aux acc
  | .itec acc cond ref => EnvPart.itec cond ref :: aux acc)
  List.reverse ∘ aux
