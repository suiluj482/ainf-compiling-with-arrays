import Polara.Codegeneration.Utils
import Polara.Optimizations.Vectorization

def Const0.tmgenPy (const0: Const0 α): String := match const0 with
| .litlZ => "0"
| .litlE => "[]"
| _ => s!"{const0}"

def Const1.tmgenPy (a: String): Const1 α₁ α → String
| .normCdf => "normCdf"        ++ s!"({a})"
| .sqrt => "math.sqrt"         ++ s!"({a})"
| .log => "math.log"           ++ s!"({a})"
| .exp => "math.exp"           ++ s!"({a})"
| .fst => s!"{a}[0]"
| .snd => s!"{a}[1]"
| .i2n => "idx2int"            ++ s!"({a})"
| .n2f => "float"              ++ s!"({a})"
| .sumf
| .suml => "sum"                ++ s!"({a})"
| .arr2list => s!"{a}"

def Const2.tmgenPy (a: String) (b: String): Const2 α₁ α₂ α → String
| arithOp op => s!"{a} {op} {b}"
| linOp op => s!"{a} {op} {b}"
| linScale op => s!"{a} {op} {b}"
| lt => s!"{a} < {b}"
| maxf => s!"max({a}, {b})"
| addi => s!"{a} + {b}"
| eqi  => s!"{a} == {b}"
| tup  => s!"({a}, {b})"
| app  => s!"{a}({b})"
| get  => s!"{a}[{b}]"
| cons => s!"[{a}] + {b}"
| append => s!"{a} + {b}"
| zipL => s!"list(zip({a}, {b}))"
| mapL => s!"list(map({b}, {a}))"
| foldL => s!"fold({b}[0], {a}, {b}[1])"
| foldA => s!"fold({b}[0], {a}, {b}[1])"

def Tm.codegenPy' : Tm VPar α → VParM String
| var i => return i.toString
| err => return "None"
| cst0 k => return k.tmgenPy
| cst1 k a => return k.tmgenPy s!"({(← a.codegenPy')})"
| cst2 k a b => return k.tmgenPy s!"({← a.codegenPy'})" s!"({← b.codegenPy'})"
| abs f => do
  let v := (←VParM.parVPar) _
  return s!"(lambda {v}: {←(f v).codegenPy'})"
| bld (n:=n) f => do
  let v := (←VParM.parVPar) _
  return s!"[(lambda {v}: {←(f v).codegenPy'})({v}) for {v} in range(0,{n})]" -- python closure only captures vars not values
| bnd e f => do
  let x := (←VParM.varVPar) _
  return s!"(lambda {x}={←e.codegenPy'}: \n{←(f x).codegenPy'})()"
| ite cond a b =>
  return s!"({<- a.codegenPy'} if {<- cond.codegenPy'} else {<- b.codegenPy'})"

-- generates a python expression
-- devectorize because python does not support vector operations
def Tm.codegenPy (t: Tm VPar α): String := Tm.codegenPy' t.devectorize |>.startZero

instance genPython: Codegen "Python" :=
  ⟨(s!"print({Tm.codegenPy ·})")⟩
