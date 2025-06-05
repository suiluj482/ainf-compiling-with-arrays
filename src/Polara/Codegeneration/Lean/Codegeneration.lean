import Polara.Optimizations.NbE
import Polara.Syntax.Index

open Prim

-- namespace LeanCodegen

def Ty.gen: Ty → String
  | flt  => "Float"
  | nat  => "Nat"
  | Ty.idx i => s!"Fin ({i}+1)"
  | a~>b => s!"({a.gen} → Except String {b.gen})"
  | a××b => s!"({a.gen} × {b.gen})"
  | array _n b => s!"(Array {b.gen})"

-- #eval Ty.nat              |> Ty.gen
-- #eval Ty.flt ~> Ty.nat    |> Ty.gen
-- #eval (Ty.nat ×× Ty.nat)  |> Ty.gen
-- #eval (Ty.array 2 Ty.nat) |> Ty.gen

def Env.tygen: String → Env → String
  | s, .nil        => s
  | s, .func Γ α _i => Γ.tygen s!"({α.gen} → Except String {s})"
  | s, .forc Γ _n _i => Γ.tygen s!"(Array {s})"
  | s, .itec Γ _i _m => Γ.tygen s!"(Except String {s})"

-- #eval Env.nil.tygen ""
-- #eval Env.func (Env.nil) Ty.nat (Par.mk 0) |>.tygen ""
-- #eval Env.forc (Env.nil) 2 (Par.mk 0) |>.tygen ""
-- #eval Env.itec (Env.nil) (VPar.v (Var.mk 0)) true |>.tygen ""

def Env.withargs (s: String): Env → String -- Env wo wir sind mit wo wir variable benutzen wollen vergleichen
  | nil       => s
  | func Γ _α i => s!"(<- {Γ.withargs s} {i.pretty})"
  | forc Γ _n i => s!"({Γ.withargs s})[{i.pretty}]!"
  | itec Γ _i _b => s!"(<- {Γ.withargs s})"

-- #eval Env.nil.withargs "."
-- #eval Env.func (Env.nil) Ty.nat (Par.mk 0) |>.withargs "."
-- #eval Env.forc (Env.nil) 2 (Par.mk 0) |>.withargs "."
-- #eval Env.itec (Env.nil) (VPar.v (Var.mk 0)) true |>.withargs "."

def Var.tmgen (_Γ: Env) (x: Var α): Orig String := do
  match x.lookupEnv (<- read) with -- <- Zugriff aufs Orignal
  | some Δ => return Δ.withargs x.pretty -- variable übergeben
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
  | fst => "Prod.fst"
  | snd => "Prod.snd"
  | i2n => "Fin.val"
  | n2f => "Float.ofNat"
  | sum (n:=n) => s!"Array.esum {n}"

def Const2.tmgen (a: String) (b: String): Const2 α₁ α₂ α → String
  | addn => s!"{a} + {b}" | muln => s!"{a} * {b}"
  | addf => s!"{a} + {b}" | subf => s!"{a} - {b}" | mulf => s!"{a} * {b}" | divf => s!"{a} / {b}" | maxf => s!"max {a} {b}"
  | addi => s!"{a}.add' {b}"
  | tup  => s!"({a}, {b})"
  | app  => s!"<- {a} {b}"
  | get  => s!"{a}[{b}]!"

def Env.wrap (s: String): Env → Orig String -- neue variable in env definieren gegenteil withargs
| .nil            => return s
| .func Γ α i     => wrap s!"(fun {i.pretty}:{α.gen} => return {s})" Γ
| .forc Γ n i     => wrap s!"(<- Array.ebuild {n} (fun {i.pretty} => return {s}))" Γ
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

def codegenRec (k: String → String): AINF α → Orig String -- todo
| .ret x => return s!"(return {(k x.pretty)}: Except String ({α.gen}))"
| .bnd (α:=β) Γ x v e => return (
  s!"let {x.pretty}: {Γ.tygen (β.gen)} :=\n  {<- Γ.wrap (<- v.tmgen Γ)}\n" ++
  (<- codegenRec k e))

def AINF.codegen (k: String → String) (a: AINF α): String := s!"do \n{(codegenRec k a a)}" -- kontinuation return x für letzte zeile
