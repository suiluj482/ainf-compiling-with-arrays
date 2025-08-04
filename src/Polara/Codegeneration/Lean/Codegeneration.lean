import Polara.Codegeneration.Utils


def Ty.gen': Ty → String
  | flt  => "Float"
  | nat  => "Nat"
  | lin => "Float"
  | Ty.idx i => s!"(Fin ({i}+1))"
  -- necessary because lazy
  | a~>b => s!"({a.gen'} → Except String {b.gen'})"
  | a××b => s!"({a.gen'} × {b.gen'})"
  | array n b => s!"(Vector {b.gen'} {n})"
-- for Tm.err
def Ty.gen (t: Ty): String := s!"Except String {t.gen'}"

def Const1.tmgen: Const1 α₁ α → String
  | normCdf => "Float.normCdf"
  | sqrt => "Float.sqrt"
  | log => "Float.log"
  | exp => "Float.exp"
  | fst => "Prod.fst"
  | snd => "Prod.snd"
  | i2n => "Fin.val"
  | n2f => "Float.ofNat"
  | sumf
  | suml => "Vector.esum"

def Const2.tmgen (a: String) (b: String): Const2 α₁ α₂ α → String
  | arithOp op => s!"{a} {op} {b}"
  | linOp op => s!"{a} {op} {b}"
  | linScale op => s!"{a} {op} {b}"

  | lt => s!"{a} < {b}"
  | maxf => s!"max {a} {b}"
  | addi => s!"{a}.add' {b}"
  | tup  => s!"({a}, {b})"
  | app  => s!"← {a} {b}"
  | get  => s!"{a}[{b}]!"

def Tm.codegen': Tm VPar α → ReaderM (Nat × Nat) String
  | err => return "Except.error"
  | var i => return match i with
    | .v v => v.toString
    | .p p => s!"(return {p})"
  | cst0 k => return s!"return {k}"
  | cst1 k a => return s!"return {k.tmgen} (←{(← a.codegen')})"
  | cst2 k a b => return "return " ++ k.tmgen s!"(←{<- a.codegen'})" s!"(←{<- b.codegen'})"
  | abs (α:=γ) f => do
    let (i,j) <- read
    let v := VPar.p (.mk j)
    return s!"(return fun {v}:{γ.gen'} => {(f v).codegen' (i,j+1)})"
  | bld (n:=n) f => do
    let (i,j) <- read
    let v := VPar.p (.mk j)
    return  s!"(Vector.ebuild {n} fun {v} => {(f v).codegen' (i, j+1)})"
  | bnd (α:=β) e f => do
    let (i,j) <- read
    let x := VPar.v (.mk i)
    return s!"let {x}: {β.gen} := {e.codegen' (i,j)}; \n{(f x).codegen' (i+1,j)}"
  | ite cond a b =>
    return s!"(if (←{← cond.codegen'}) != 0 then {<- a.codegen'} else {<- b.codegen'})"

def Tm.codegen (t: Tm VPar α): String := s!"(do \n{Tm.codegen' t (0,0)})"
