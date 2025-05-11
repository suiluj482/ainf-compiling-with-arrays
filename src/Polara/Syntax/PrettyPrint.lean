import Polara.Syntax.Definitions

------------------------------------------------------------------------------------------
-- Tm ToString
------------------------------------------------------------------------------------------

def String.indent (s: String): String := "\n  " ++ s.replace "\n" "\n  "
def String.parens (s: String): String := s!"({s})"

def Ty.pretty : Ty → String
  | flt  => "Float"
  | nat  => "Nat"
  | idx i => s!"Idx {i}"
  | a~>b => s!"({a.pretty} ~> {b.pretty})"
  | a××b => s!"({a.pretty} ×× {b.pretty})"
  | array n b => s!"(array {n} {b.pretty})"

def Const0.pretty : Const0 α → String
  | litn n => ToString.toString n
  | litf f => ToString.toString f
  | liti i => ToString.toString i.val

def Const1.pretty : Const1 α₁ α → String
  | exp => "exp"
  | sqrt => "sqrt"
  | log => "log"
  | normCdf => "normCdf"
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

-- pretty print
--  (next Var number, next Param number)
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
  | bld (n:=n) f => do
    let (i,j) <- read
    let tmp: String := (f (.p (.mk j))).pp (i,j+1)
    return s!"for i{j}:{n} =>" ++ tmp.indent
  | bnd e f => do
    let (i,j) <- read
    let xx := VPar.v (.mk i)
    let tmp1: String := e.pp (i,j)
    let tmp2: String := (f xx).pp (i+1,j)
    return s!"let {xx.pretty} = {tmp1};\n{tmp2}"
  | ite a b c => return s!"(if {<- a.pp} then {<- b.pp} else {<- c.pp})"

def Tm.pretty (t: Tm VPar α): String := Tm.pp t (0,0)
def Tm.toString (t: Tm VPar α) := t.pretty
instance: ToString (Tm VPar α) := ⟨Tm.toString⟩

------------------------------------------------------------------------------------------
-- AINF ToString
------------------------------------------------------------------------------------------

def Env.patmat : String → Env → String
  | s, .nil             => s
  | s, .func Γ α i      => Γ.patmat s!"fun {i.pretty}:{α.pretty}, {s}"
  | s, .forc Γ i (n:=n) => Γ.patmat s!"for {i.pretty}:{n}, {s}"
  | s, .itec Γ i true   => Γ.patmat s!"if {i.pretty}!=0, {s}"
  | s, .itec Γ i false  => Γ.patmat s!"if {i.pretty}==0, {s}"

def Env.pretty: Env → String := Env.patmat ""

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

def AINF.toString : AINF α → String | e => e.pretty id
instance : ToString (AINF α) where toString x := x.toString
