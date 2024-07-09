import Polara.NbE
import Polara.Syntax

------------------------------------------------------------------------------------------
-- arrays
------------------------------------------------------------------------------------------

def Array.ebuild: Nat → (Nat → Except String α) → Except String (Array α)
| n, f => ((mkArray n 0).mapIdx fun i _x => f i).mapM fun i => i

class Monoid (α: Type) where
  default : α
  combine : α → α → α

instance : Monoid Float where
  default := 0
  combine := (. + .)

def Array.esum [Inhabited α] [Monoid α]: Nat → (Array α) → α
| n, f => ((mkArray n 0).mapIdx fun i _x => f.get! i).foldl Monoid.combine Monoid.default

def Fin.add' : Fin n → Fin m → Fin (n+m-1)
| ⟨x, hx⟩, ⟨y, hy⟩ => ⟨x+y,
  let ⟨ x', hx' ⟩ := Nat.le.dest hx;
  let ⟨ y', hy' ⟩ := Nat.le.dest hy;
  Nat.le.intro (k := x' + y') (by simp_arith! [←hx', ←hy']) ⟩

------------------------------------------------------------------------------------------
-- codegen
------------------------------------------------------------------------------------------

open Prim

def Ty.gen: Ty → String
  | flt  => "Float"
  | nat  => "Nat"
  | idx i => s!"Fin ({i}+1)"
  | a~>b => s!"({a.gen} → Except String {b.gen})"
  | a××b => s!"({a.gen} × {b.gen})"
  | array _n b => s!"(Array {b.gen})"

def Env.tygen: String → Env → String
  | s, .nil        => s
  | s, .func Γ α _i => Γ.tygen s!"({α.gen} → Except String {s})"
  | s, .forc Γ _n _i => Γ.tygen s!"(Array {s})"
  | s, .itec Γ _i _m => Γ.tygen s!"(Except String {s})"

def Env.withargs (s: String): Env → String
  | nil       => s
  | func Γ _α i => s!"(<- {Γ.withargs s} {i.pretty})"
  | forc Γ _n i => s!"({Γ.withargs s})[{i.pretty}]!"
  | itec Γ _i _b => s!"(<- {Γ.withargs s})"

def Var.tmgen (Γ: Env) (x: Var α): Orig String := do
  match lookupEnv x (<- read) with
  | some Δ => return Δ.withargs x.pretty
  | none   => return "(" ++ x.pretty ++ " ???)"
def VPar.tmgen (Γ: Env) (x: VPar α): Orig String :=
  match x with
  | .v x => x.tmgen Γ
  | .p x => return x.pretty

def Const1.tmgen: Const1 α₁ α → String
  | normCdf => "Float.normCdf"
  | sqrt => "Float.sqrt"
  | log => "Float.log"
  | exp => "Float.exp"
  | fst => "Float.fst"
  | snd => "Float.snd"
  | i2n => "Fin.val"
  | n2f => "Float.ofNat"
  | sum => "Array.esum"

def Const2.tmgen (a: String) (b: String): Const2 α₁ α₂ α → String
  | addn => s!"{a} + {b}" | muln => s!"{a} * {b}"
  | addf => s!"{a} + {b}" | subf => s!"{a} - {b}" | mulf => s!"{a} * {b}" | divf => s!"{a} / {b}" | maxf => s!"max {a} {b}"
  | addi => s!"{a} + {b}"
  | tup  => s!"({a}, {b})"
  | app  => s!"<- {a} {b}"
  | get  => s!"{a}[{b}]!"

def Env.wrap (s: String): Env → Orig String
| .nil            => return s
| .func Γ α i     => wrap s!"(fun {i.pretty}:{α.gen} => return {s})" Γ
| .forc Γ n i     => wrap s!"(<- Array.ebuild {n} fun {i.pretty} => return {s})" Γ
| .itec Γ i true  => do wrap s!"(<- if {<- i.tmgen Γ} != 0
      then return Except.ok ({s})
      else return Except.error \"conditional\")" Γ
| .itec Γ i false => do wrap s!"(<- if {<- i.tmgen Γ} == 0
      then return Except.ok ({s})
      else return Except.error \"conditional\")" Γ

def Prim.tmgen (Γ: Env): Prim α → Orig String
| err => return "ERROR"
| cst0 k => return k.pretty
| cst1 k a => return k.tmgen ++ " " ++ (<- a.tmgen Γ) ++ ""
| cst2 k a b => return k.tmgen (<- a.tmgen Γ) (<- b.tmgen Γ)
| var i => return i.pretty
| abs (α:=γ) i e => return s!"(fun {i.pretty}:{γ.gen} => return {<- e.tmgen (.func Γ _ i)})"
| bld (n:=n) i e => return  s!"(<- Array.ebuild {n} fun {i.pretty} => return {<- e.tmgen (.forc Γ n i)})"
| .ite a b c => return s!"(<- if {<- a.tmgen Γ} != 0
    then return {<- b.tmgen (.itec Γ a true )}
    else return {<- c.tmgen (.itec Γ a false)})"

def codegenRec (k: String → String): AINF α → Orig String
| .ret x => return k x.pretty
| .bnd (α:=β) Γ x v e => return (
  s!"  let {x.pretty}: {Γ.tygen (β.gen)} :=\n    {<- Γ.wrap (<- v.tmgen Γ)}\n" ++
  (<- codegenRec k e))

def AINF.codegen (k: String → String) (a: AINF α): String := codegenRec k a a
