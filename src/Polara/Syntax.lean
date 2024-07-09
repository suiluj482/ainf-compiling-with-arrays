inductive Ty
  | nat : Ty
  | idx : Nat → Ty
  | flt : Ty
  | arrow : Ty → Ty → Ty
  | product : Ty → Ty → Ty
  | array : Nat → Ty → Ty
  deriving DecidableEq, Inhabited, BEq
  open Ty
  infixr : 80 "~>" => Ty.arrow
  infixr : 70 "××" => Ty.product

inductive Const0 : Ty → Type
  | litn : Nat → Const0 nat
  | litf : Float → Const0 flt
  | liti : Fin (n+1) → Const0 (idx n)
  deriving BEq
  open Const0

inductive Const1 : Ty → Ty → Type
  | exp  : Const1 flt flt
  | sqrt : Const1 flt flt
  | log  : Const1 flt flt
  | normCdf : Const1 flt flt
  | fst : Const1 (α ×× β) α
  | snd : Const1 (α ×× β) β
  | sum : Const1 (array n α) α
  | i2n  : Const1 (idx n) nat
  | n2f  : Const1 nat flt
  deriving BEq
  open Const1

inductive Const2 : Ty → Ty → Ty → Type
  | addn : Const2 nat nat nat
  | muln : Const2 nat nat nat
  | addf : Const2 flt flt flt
  | subf : Const2 flt flt flt
  | mulf : Const2 flt flt flt
  | divf : Const2 flt flt flt
  | maxf : Const2 flt flt flt
  | addi : Const2 (idx n) (idx m) (idx (n+m-1))
  | get : Const2 (array n a) (idx n) a
  | tup : Const2 α β (α ×× β)
  | app : Const2 (α~>β) α β
  deriving BEq
  open Const2

inductive Tm (Γ: Ty → Type): Ty → Type
  | err : Tm Γ a
  | var : Γ α → Tm Γ α
  | cst0 : Const0          α →                     Tm Γ α
  | cst1 : Const1 α₁       α → Tm Γ α₁ →           Tm Γ α
  | cst2 : Const2 α₁ α₂    α → Tm Γ α₁ → Tm Γ α₂ → Tm Γ α
  | abs : (Γ α → Tm Γ β) → Tm Γ (α ~> β)
  | bld : (Γ (idx n) → Tm Γ α) → Tm Γ (array n α)
  | bnd : Tm Γ α → (Γ α → Tm Γ β) → Tm Γ β
  | ite : Tm Γ nat → Tm Γ β → Tm Γ β → Tm Γ β
  open Tm
  infixl:65 " @@ " => Tm.cst2 Const2.app

inductive Var : Ty → Type
  | mk : Nat → Var α
  deriving DecidableEq, BEq

inductive Par : Ty → Type
  | mk : Nat → Par α
  deriving DecidableEq, BEq

inductive VPar α
  | v : Var α → VPar α
  | p : Par α → VPar α
  deriving DecidableEq, BEq

inductive Env : Type
  | nil  : Env
  | func : Env → (α:Ty) → Par α → Env
  | forc : Env → (n:Nat) → Par (idx n) → Env
  | itec : Env → VPar nat → Bool → Env

inductive Prim : Ty → Type
  | cst0 : Const0 α → Prim α
  | cst1 : Const1 α₁ α → VPar α₁ → Prim α
  | cst2 : Const2 α₁ α₂ α → VPar α₁ → VPar α₂ → Prim α
  | err : Prim α
  | var : VPar α → Prim α
  | abs : Par α → VPar β → Prim (α ~> β)
  | ite : VPar nat → VPar α → VPar α → Prim α
  | bld : Par (idx n) → VPar α → Prim (array n α)

inductive AINF : Ty → Type
  | ret : VPar α → AINF α
  | bnd : Env → Var α → Prim α → AINF β → AINF β

------------------------------------------------------------------------------------------
-- Util
------------------------------------------------------------------------------------------

def AINF.size : AINF α → Nat
  | .ret _ => 0
  | .bnd _ _ _ p => p.size + 1

def ListMap (A B: Ty → Type) := List ((γ : Ty) × A γ × B γ)

def ListMap.lookup [∀ x:Ty, BEq (K x)] : ListMap K V → K α → Option (V α)
  | [],          _ => none
  | ⟨β,k,v⟩::ys, i => if h: β=α then if k == h▸i then some (h▸v)
                      else lookup ys i else lookup ys i

@[reducible] def Orig α := ∀ {β}, ReaderM (AINF β) α
def lookupEnv (x: Var α) : AINF β → Option Env
  | .ret _y => none
  | .bnd (α:=γ) Γ y _ k =>
    if h: γ=α then if h▸ y==x then Γ
    else lookupEnv x k else lookupEnv x k

------------------------------------------------------------------------------------------
-- Tm ToString
------------------------------------------------------------------------------------------

def String.indent (s: String): String := "\n  " ++ s.replace "\n" "\n  "
def String.parens (s: String): String := s!"({s})"

def Const0.pretty : Const0 α → String
  | litn n => ToString.toString n
  | litf f => ToString.toString f
  | liti i => ToString.toString i.val

def Const1.pretty : Const1 α₁ α → String
  | normCdf => "normCdf"
  | sqrt => "sqrt"
  | log => "log"
  | exp => "exp"
  | fst => "fst"
  | snd => "snd"
  | sum => "sum"
  | i2n => "val"
  | n2f => "ofNat"

def Const2.pretty (a: String) (b: String): Const2 α₁ α₂ α → String
  | addn => s!"{a} + {b}" | muln => s!"{a} * {b}"
  | addf => s!"{a} + {b}" | subf => s!"{a} - {b}" | mulf => s!"{a} * {b}" | divf => s!"{a} / {b}" | maxf => s!"max {a} {b}"
  | addi => s!"{a} + {b}"
  | tup  => s!"({a}, {b})"
  | app  => s!"{a} {b}"
  | get  => s!"{a}[{b}]"

def Par.pretty : Par α → String
  | mk x => "i" ++ x.repr
def Var.pretty : Var α → String
  | .mk x => "x" ++ x.repr
def VPar.pretty : VPar α → String
  | .v x => x.pretty
  | .p i => i.pretty

def Tm.pp : Tm VPar α → ReaderM (Nat × Nat) String
  | var i => return i.pretty
  | err => return "ERROR"
  | cst0 k => return k.pretty
  | cst1 k a => return (k.pretty ++ " " ++ (<- a.pp)).parens
  | cst2 k b a => return (k.pretty (<- b.pp) (<- a.pp)).parens
  | abs f => do
    let (i,j) <- read
    let tmp: String := (f (.p (.mk j))).pp (i,j+1)
    return s!"fun i{j} =>" ++ tmp.indent
  | bld f => do
    let (i,j) <- read
    let tmp: String := (f (.p (.mk j))).pp (i,j+1)
    return s!"for i{j} =>" ++ tmp.indent
  | bnd e f => do
    let (i,j) <- read
    let xx := VPar.v (.mk i)
    let tmp1: String := e.pp (i,j)
    let tmp2: String := (f xx).pp (i+1,j)
    return s!"let {xx.pretty} = {tmp1};\n{tmp2}"
  | ite a b c => return s!"(if {<- a.pp} then {<- b.pp} else {<- c.pp})"

------------------------------------------------------------------------------------------
-- AINF ToString
------------------------------------------------------------------------------------------

def Ty.pretty : Ty → String
  | flt  => "Float"
  | nat  => "Nat"
  | idx i => s!"Idx {i}"
  | a~>b => s!"({a.pretty} → {b.pretty})"
  | a××b => s!"({a.pretty} × {b.pretty})"
  | array n b => s!"({n} => {b.pretty})"

def Env.patmat : String → Env → String
  | s, .nil             => s
  | s, .func Γ α i      => Γ.patmat s!"fun {i.pretty}:{α.pretty}, {s}"
  | s, .forc Γ i (n:=n) => Γ.patmat s!"for {i.pretty}:{n}, {s}"
  | s, .itec Γ i true   => Γ.patmat s!"if {i.pretty}!=0, {s}"
  | s, .itec Γ i false  => Γ.patmat s!"if {i.pretty}==0, {s}"

def Prim.pretty: Prim α → String
  | .err => "ERROR"
  | .cst0 k => k.pretty
  | .cst1 k a => k.pretty ++ " " ++ a.pretty ++ ""
  | .cst2 k a b => k.pretty ("" ++ a.pretty ++ "") ("" ++ b.pretty ++ "")
  | .var i => i.pretty
  | .abs (α:=γ) i e => s!"fun {i.pretty}:{γ.pretty}, " ++ (e.pretty).replace "\n" "\n  "
  | .bld (n:=n) i e => s!"for {i.pretty}:{n}, {e.pretty}"
  | .ite a b c => "if " ++ a.pretty ++ " != 0 then " ++ b.pretty ++ " else " ++ c.pretty

def AINF.pretty (k: String → String): AINF α → String
  | .ret x => k x.pretty
  | .bnd (α:=β) Γ x v e =>
    let string := s!"({x.pretty} : {β.pretty} := {v.pretty})"
    s!"  let {Γ.patmat string}\n" ++
    e.pretty k
