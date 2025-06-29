import Polara.Codegeneration.Utils

def Const0.tmgenJax (const0: Const0 α): String := s!"jnp.array({const0.pretty})"

def Const1.tmgenJax (a: String): Const1 α₁ α → String
  | normCdf => "normCdf" ++ s!"({a})"
  | sqrt => "jnp.sqrt"         ++ s!"({a})"
  | log => "jnp.log"           ++ s!"({a})"
  | exp => "jnp.exp"           ++ s!"({a})"
  | fst => s!"{a}[0]"
  | snd => s!"{a}[1]"
  | i2n => "idx2int"            ++ s!"({a})"
  | n2f => s!"{a}.astype(float)"
  | sumf
  | suml => "jnp.sum"            ++ s!"({a})"

def Const2.tmgenJax (a: String) (b: String): Const2 α₁ α₂ α → String
  | arithOp op => s!"{a} {op.pretty} {b}"
  | linOp op => s!"{a} {op.pretty} {b}"
  | linScale op => s!"{a} {op.pretty} {b}"
  | maxf => s!"max({a}, {b})"
  | addi => s!"{a} + {b}"
  | tup  => s!"({a}, {b})"
  | app  => s!"{a}({b})"
  | get  => s!"{a}[{b}]"

partial def Tm.codegenJax' : Tm VPar α → ReaderM (Nat × Nat) String
  -- | err => return "None"
  | err => (Tm.inst α).codegenJax' -- guranteed termination because inst has no error but how to prove this?
  | var i => return i.pretty
  | cst0 k => return k.tmgenJax
  | cst1 k a => return k.tmgenJax s!"({(← a.codegenJax')})"
  | cst2 k a b => return k.tmgenJax s!"({← a.codegenJax'})" s!"({← b.codegenJax'})"
  | abs f => do
    let (i,j) <- read
    let v := VPar.p (.mk j)
    return s!"(lambda {v.pretty}: {(f v).codegenJax' (i,j+1)})"
  | bld (n:=n) f => do
    let (i,j) <- read
    let v := VPar.p (.mk j)
    return s!"(jax.vmap(lambda {v.pretty}: {(f v).codegenJax' (i, j+1)})(jnp.arange({n})))"
  | bnd e f => do
    let (i,j) <- read
    let x := VPar.v (.mk i)
    return s!"let({x.pretty} := {e.codegenJax' (i,j)}, \n{(f x).codegenJax' (i+1,j)})"
  | ite cond a b =>
    return s!"(lax.cond({← cond.codegenJax'} != 0, lambda: {<- a.codegenJax'}, lambda: {<- b.codegenJax'}))"

-- generates a python expression
def Tm.codegenJax (t: Tm VPar α): String := Tm.codegenJax' t (0,0)

------------------------------------------------------
-- todo when to use jit
-- jit doesn't work with stacked functions
-- -> compress into function with multiple arguments, max be more efficient in general

-- test joining functions together
def Tm.codegenJaxJit (t: Tm VPar α): String :=
  let rec tmp: Ty → Nat := λ
    | .arrow _ β => tmp β + 1
    | _ => 0
  let numArgs := tmp α
  let args :=
    List.range numArgs |>.foldl (· ++ s!", j{·}") "" |>.drop 2
  let calls: String :=
    List.range numArgs |>.foldl (· ++ s!"(j{·})") ""

  let t := t.codegenJax
  s!"jit(lambda {args}:{t}{calls})"


-- def test: Tm VPar (Ty.nat ~> Ty.nat ~> Ty.nat) :=
--   fun' x => fun' y => Tm.var x + Tm.var y

-- def test': Tm VPar Ty.nat :=
--   tlitn 42

-- #eval test'.codegenJaxJit
