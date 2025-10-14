import Polara.Syntax.Definitions

------------------------------------------------------------------------------------------
-- Tm ToString
------------------------------------------------------------------------------------------

def Ty.toString : Ty → String
| flt  => "Float"
| nat  => "Nat"
| lin => "Lin"
| idx i => s!"Idx {i}"
| a~>b => s!"({a.toString} ~> {b.toString})"
| a××b => s!"({a.toString} ×× {b.toString})"
| array n b => s!"(array {n} {b.toString})"
| unit => "Unit"
| list α => s!"(list {α.toString})"
instance: ToString Ty := ⟨Ty.toString⟩

def Const0.toString : Const0 α → String
| litn n => ToString.toString n
| litf f => ToString.toString f
| liti i => ToString.toString i.val
| litlZ => "0"
| litu => "()"
| litE => "[]"
instance: ToString (Const0 α) := ⟨Const0.toString⟩

def Const1.toString : Const1 α₁ α → String
| exp => "exp"
| sqrt => "sqrt"
| log => "log"
| normCdf => "normCdf"
| fst => "fst"
| snd => "snd"
| sumf => "sum"
| suml => "sum"
| i2n => "i2n"
| n2f => "n2f"
| arr2list => "toList"
instance: ToString (Const1 α₁ α) := ⟨Const1.toString⟩

def ArithOp.toString : ArithOp → String
| add => "+"
| sub => "-"
| mul => "*"
| div => "/"
instance: ToString ArithOp := ⟨ArithOp.toString⟩

def AddOp.toString : AddOp → String
| add => "+"
| sub => "-"
instance: ToString AddOp := ⟨AddOp.toString⟩

def MulOp.toString : MulOp → String
| mul => "*"
| div => "/"
instance: ToString MulOp := ⟨MulOp.toString⟩

def Const2.toString (a: String) (b: String): Const2 α₁ α₂ α → String
| arithOp op => s!"{a} {op.toString} {b}"
| linOp op => s!"{a} {op.toString} {b}"
| linScale op => s!"{a} {op.toString} {b}"
| addi => s!"{a} + {b}"
| eqi => s!"{a} == {b}"
-- | fori => s!"foldi {a} {b}"
| lt => s!"{a} < {b}"
| maxf => s!"max {a} {b}"
| tup  => s!"({a}, {b})"
| app  => s!"{a} {b}"
| get  => s!"{a}[{b}]"
| cons => s!"{a} :: {b}"
| append => s!"{a} ++ {b}"
| zipL => s!"{a}.zip {b}"
| mapL => s!"{a}.map {b}"
| aFoldL => s!"{a}.fold {b}"
| aFoldA => s!"{a}.fold {b}"

def Par.toString : Par α → String
  | mk x => "i" ++ x.repr
instance: ToString (Par α) := ⟨Par.toString⟩
def Var.toString : Var α → String
  | .mk x => "x" ++ x.repr
instance: ToString (Var α) := ⟨Var.toString⟩
def VPar.toString : VPar α → String
  | .v x => x.toString
  | .p i => i.toString
instance: ToString (VPar α) := ⟨VPar.toString⟩

-- toString print
--  (next Var number, next Param number)
def Tm.pp : Tm VPar α → ReaderM (Nat × Nat) String
  | var i => return i.toString
  | err => return "ERROR"
  | cst0 k => return k.toString
  | cst1 k a => return (k.toString ++ " " ++ (<- a.pp)).parens
  | cst2 k b a => return (k.toString (<- b.pp) (<- a.pp)).parens
  | abs f => do
    let (i,j) <- read
    let tmp: String := (f (.p (.mk j))).pp (i,j+1)
    return s!"(fun i{j} =>{tmp.indent})"
  | bld (n:=n) f => do
    let (i,j) <- read
    let tmp: String := (f (.p (.mk j))).pp (i,j+1)
    return s!"for i{j}:{n} =>" ++ tmp.indent
  | bnd e f => do
    let (i,j) <- read
    let xx := VPar.v (.mk i)
    let tmp1: String := e.pp (i,j)
    let tmp2: String := (f xx).pp (i+1,j)
    return s!"(let {xx.toString} := {tmp1};\n{tmp2})"
  | ite a b c => return s!"(if {<- a.pp} then {<- b.pp} else {<- c.pp})"

def Tm.toString (t: Tm VPar α): String := Tm.pp t (0,0)
instance: ToString (Tm VPar α) := ⟨Tm.toString⟩

------------------------------------------------------------------------------------------
-- AINF ToString
------------------------------------------------------------------------------------------
def EnvPart.toString: EnvPart → String
  | .func α i      => s!"fun {i.toString}:{α.toString}"
  | .forc i (n:=n) => s!"for {i.toString}:{n}"
  | .itec i true   => s!"if {i.toString}!=0"
  | .itec i false  => s!"if {i.toString}==0"
instance : ToString EnvPart := ⟨EnvPart.toString⟩
def Env.toString (env: Env): String :=
  env.toStringSep ", "
instance: ToString Env := ⟨Env.toString⟩

def Prim.toString: Prim α → String
  | .err => "ERROR"
  | .cst0 k => k.toString
  | .cst1 k a => k.toString ++ " " ++ a.toString ++ ""
  | .cst2 k a b => k.toString ("" ++ a.toString ++ "") ("" ++ b.toString ++ "")
  | .var i => i.toString
  | .abs (α:=γ) i e => s!"fun {i.toString}:{γ.toString}, " ++ (e.toString).replace "\n" "\n  "
  | .bld (n:=n) i e => s!"for {i.toString}:{n}, {e.toString}"
  | .ite a b c => "if " ++ a.toString ++ " != 0 then " ++ b.toString ++ " else " ++ c.toString
instance : ToString (Prim α) := ⟨Prim.toString⟩

def Bnd.toString: Bnd → String
| ⟨⟨α, var⟩, env, prim⟩ => s!"let {env} ({var} : {α} := {prim})"
instance : ToString Bnd := ⟨Bnd.toString⟩

def AINF.toString: AINF α → String
| (bnds, ret) => s!"{bnds.map Bnd.toString |>.toStringSep "\n" |>.indent}\n{ret}"
instance : ToString (AINF α) where toString x := x.toString
