import Polara.Codegeneration.Utils


def Ty.gen: Ty → String
  | flt  => "Float"
  | nat  => "Nat"
  | Ty.idx i => s!"Fin ({i}+1)"
  | a~>b => s!"({a.gen} → Except String {b.gen})"
  | a××b => s!"({a.gen} × {b.gen})"
  | array _n b => s!"(Array {b.gen})"

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

def Tm.codegen': Tm VPar α → ReaderM (Nat × Nat) String
  | err => return "Except.error"
  | var i => return i.pretty
  | cst0 k => return k.pretty
  | cst1 k a => return s!"{k.tmgen} {(← a.codegen')}"
  | cst2 k a b => return k.tmgen (<- a.codegen') (<- b.codegen')
  | abs (α:=γ) f => do
    let (i,j) <- read
    let v := VPar.p (.mk j)
    return s!"(fun {v.pretty}:{γ.gen} => return {(f v).codegen' (i,j+1)})"
  | bld (n:=n) f => do
    let (i,j) <- read
    let v := VPar.p (.mk j)
    return  s!"(<- Array.ebuild {n} fun {v.pretty} => return {(f v).codegen' (i, j+1)})"
  | bnd (α:=β) e f => do
    let (i,j) <- read
    let x := VPar.v (.mk i)
    return s!"let {x.pretty}: {β.gen} := {e.codegen' (i,j)}, \n{(f x).codegen' (i+1,j)})"
  | ite cond a b =>
    return s!"(← if {← cond.codegen'} != 0 then return {<- a.codegen'} else return {<- b.codegen'}))"

def Tm.codegen (t: Tm VPar α): String := Tm.codegen' t (0,0)

-- todo think about Except
