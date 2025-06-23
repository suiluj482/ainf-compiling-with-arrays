import Polara.Utils.Index

-- Type
inductive Ty
  | nat : Ty                  -- natural number
  | idx : Nat → Ty            -- index
  | flt : Ty                  -- float
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
  -- | mul
  | i2n  : Const1 (idx n) nat     -- indices -> nat
  | n2f  : Const1 nat flt         -- nat -> float
  deriving BEq
  open Const1

-- broadcastArrayL (boradcastArrayR) should be forbidden
inductive TypesArithOp: Ty → Ty → Ty → Type
| nats: TypesArithOp nat nat nat
| flts: TypesArithOp flt flt flt
| elementsArray (n: Nat): TypesArithOp α β γ → TypesArithOp (array n α) (array n β) (array n γ)
deriving BEq, Repr
class TypeArithOp (α β: Ty)(γ: outParam Ty) where
  type: TypesArithOp α β γ
deriving BEq, Repr

instance : TypeArithOp nat nat nat := ⟨TypesArithOp.nats⟩
instance : TypeArithOp flt flt flt := ⟨TypesArithOp.flts⟩
instance {n: Nat} {α β γ: Ty} [arithOp: TypeArithOp α β γ]: TypeArithOp (array n α) (array n β) (array n γ) :=
  ⟨TypesArithOp.elementsArray n arithOp.type⟩

inductive ArithOp: Type
| add: ArithOp
| sub: ArithOp
| mul: ArithOp
| div: ArithOp
deriving BEq, Repr

-- binary functions
inductive Const2 : Ty → Ty → Ty → Type
  | arithOp [type: TypeArithOp α β γ] (op: ArithOp): Const2 α β γ

  | addi: Const2 (idx n) (idx m) (idx (n+m))
  | maxf : Const2 flt flt flt
  | get : Const2 (array n a) (idx n) a          -- array access
  | tup : Const2 α β (α ×× β)                   -- tupple constructor
  | app : Const2 (α~>β) α β                     -- function application
-- kinda missing: zip, reduce?
  deriving BEq
  open Const2

-- #eval ((Const2.arithOp ArithOp.add): Const2 (Ty.array 5 Ty.nat) (Ty.array 5 <| Ty.array 10 Ty.nat) (Ty.array 5 <| Ty.array 10 Ty.nat))

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
