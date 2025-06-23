import Polara.Codegeneration.Utils

def Const0.tmgenPy: Const0 α → String := Const0.pretty

def Const1.tmgenPy (a: String): Const1 α₁ α → String
  | normCdf => "normCdf"        ++ s!"({a})"
  | sqrt => "math.sqrt"         ++ s!"({a})"
  | log => "math.log"           ++ s!"({a})"
  | exp => "math.exp"           ++ s!"({a})"
  | fst => s!"{a}[0]"
  | snd => s!"{a}[1]"
  | i2n => "idx2int"            ++ s!"({a})"
  | n2f => "float"              ++ s!"({a})"
  | sumf => "sum"                ++ s!"({a})"

def Const2.tmgenPy (a: String) (b: String): Const2 α₁ α₂ α → String
  | arithOp op =>
    match op with
    | .add => s!"{a} + {b}"
    | .sub => s!"{a} - {b}"
    | .mul => s!"{a} * {b}"
    | .div => s!"{a} / {b}"
  | maxf => s!"max({a}, {b})"
  | addi => s!"{a} + {b}"
  | tup  => s!"({a}, {b})"
  | app  => s!"{a}({b})"
  | get  => s!"{a}[{b}]"

def Tm.codegenPy' : Tm VPar α → ReaderM (Nat × Nat) String
  | var i => return i.pretty
  | err => return "None"
  | cst0 k => return k.tmgenPy
  | cst1 k a => return k.tmgenPy s!"({(← a.codegenPy')})"
  | cst2 k a b => return k.tmgenPy s!"({← a.codegenPy'})" s!"({← b.codegenPy'})"
  | abs f => do
    let (i,j) <- read
    let v := VPar.p (.mk j)
    return s!"(lambda {v.pretty}: {(f v).codegenPy' (i,j+1)})"
  | bld (n:=n) f => do
    let (i,j) <- read
    let v := VPar.p (.mk j)
    return s!"[{(f v).codegenPy' (i,j+1)} for {v.pretty} in range(0,{n})]"
  | bnd e f => do
    let (i,j) <- read
    let x := VPar.v (.mk i)
    return s!"let({x.pretty} := {e.codegenPy' (i,j)}, {(f x).codegenPy' (i+1,j)})"
  | ite cond a b =>
    return s!"({<- a.codegenPy'} if {<- cond.codegenPy'} else {<- b.codegenPy'})"

-- generates a python expression
def Tm.codegenPy (t: Tm VPar α): String := Tm.codegenPy' t (0,0)
