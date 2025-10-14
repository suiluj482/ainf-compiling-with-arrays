import Polara.Codegeneration.Utils


def Ty.gen': Ty → String
  | flt  => "Float"
  | nat  => "Nat"
  | lin => "Float"
  | Ty.idx i => s!"(Fin {i})"
  -- necessary because lazy
  | a~>b => s!"({a.gen'} → Option {b.gen'})"
  | a××b => s!"({a.gen'} × {b.gen'})"
  | array n b => s!"(Vector {b.gen'} {n})"
  | .unit => "Unit"
  | .list α => s!"(List {α.gen'})"
-- for Tm.err
def Ty.gen (t: Ty): String := s!"Option {t.gen'}"

def Const0.tmgen (const0: Const0 α): String := match const0 with
| liti i (n:=n) => s!"(Fin.ofNat' {n} {i})"
| litlZ => "0"
| litlE => "[]"
| _ => s!"{const0}"

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
| arr2list => "Vector.toArray.toList"

def Const2.tmgen (a: String) (b: String): Const2 α₁ α₂ α → String
| arithOp op => s!"{a} {op} {b}"
| linOp op => s!"{a} {op} {b}"
| linScale op => s!"{a} {op} {b}"

| lt => s!"Bool.toNat ({a} < {b})"
| maxf => s!"max {a} {b}"
| addi => s!"{a}.add' {b}"
| eqi  => s!"Bool.toNat ({a} == {b})"
| tup  => s!"({a}, {b})"
| app  => s!"(← (({a}: {α₁.gen'}) {b}))"
| get  => s!"{a}[{b}]!"
| cons => s!"{a} :: {b}"
| append => s!"{a} ++ {b}"
| zipL => s!"List.zip {a} {b}"
| mapL => s!"(←(({a}).mapM {b}))"
| foldL => s!"(({a}).foldlM (λ acc a => return (←({b} a)) acc) {b}.snd)"
| foldA => s!"(({a}).foldlM (λ acc a => return (←({b} a)) acc) {b}.snd)"

def Tm.codegen': Tm VPar α → ReaderM (Nat × Nat) String
  | err => return s!"(none: {α.gen})"
  | var i => return match i with
    | .v v => s!"{v}"
    | .p p => s!"(return {p})"
  | cst0 k => return s!"return {k.tmgen}"
  | cst1 k a => return s!"return {k.tmgen} (←{(← a.codegen')})"
  | cst2 k a b => return "return " ++ k.tmgen s!"(←{<- a.codegen'})" s!"(←{<- b.codegen'})"
  | abs (α:=γ) (β:=β) f => do
    let (i,j) <- read
    let v := VPar.p (.mk j)
    return s!"(return fun {v}:{γ.gen'} => do (({(f v).codegen' (i,j+1)}): {β.gen}))"
  | bld (n:=n) (α:=β) f => do
    let (i,j) <- read
    let v := VPar.p (.mk j)
    return  s!"(Vector.ebuild {n} fun {v} => do (({(f v).codegen' (i, j+1)}): {β.gen}))"
  | bnd (α:=β) e f => do
    let (i,j) <- read
    let x := VPar.v (.mk i)
    return s!"let {x}: {β.gen} := {e.codegen' (i,j)}; \n{(f x).codegen' (i+1,j)}"
  | ite cond a b =>
    return s!"(if ((←{← cond.codegen'}) != 0) \n{s!"then do {<- a.codegen'}".indent}\n{s!"else do {<- b.codegen'}".indent})"

def Tm.codegen (t: Tm VPar α): String := s!"def main (_: List String) := IO.println <| match ((do\n{
    (Tm.codegen' t (0,0)).indent.replace "←return" ""
  }\n): {α.gen}) with
| some x => ToString.toString x
| none => \"Error\"
"

instance genLean: Codegen "Lean" :=
  ⟨Tm.codegen⟩
