import Polara.Codegeneration.Utils

private def Ty.containsUnsupported: Ty → Bool
| α => α.contains (λ
  | _~>_ => true
  | α××β => α != β
  | list _ => true
  | _ => false
)

private def Const0.tmgenJax (const0: Const0 α): String := match const0 with
| .litlZ => "0"
| .litlE => "[]"
| _ => if α.containsUnsupported
  then s!"{const0}"
  else s!"jnp.array({const0})"

private def Const1.tmgenJax (a: String): Const1 α₁ α → String
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
| .arr2list => s!"to_py({a})"

private def Const2.tmgenJax (a: String) (b: String): Const2 α₁ α₂ α → String
| arithOp op => s!"{a} {op} {b}"
| linOp op => s!"{a} {op} {b}"
| linScale op => s!"{a} {op} {b}"
| lt => s!"{a} < {b}"
| maxf => s!"max({a}, {b})"
| addi => s!"{a} + {b}"
| eqi  => s!"{a} == {b}"
| tup  => if α.containsUnsupported
  then s!"({a}, {b})"
  else s!"jnp.array(({a}, {b}))"
| app  => s!"{a}({b})"
| get  => s!"{a}[{b}]"
| cons => s!"[{a}] + {b}"
| append => s!"{a} + {b}"
| zipL => s!"list(zip({a}, {b}))"
| mapL => s!"list(map({b}, {a}))"
| foldL => s!"fold({b}[0], {a}, {b}[1])"
| foldA => s!"reduce(lambda acc, x: {b}[0](x)(acc), {a}, {b}[1])"

private partial def Tm.codegenJax' : Tm VPar α → VParM String
| err => (Tm.inst α).codegenJax'
| var i => return i.toString
| cst0 k => return k.tmgenJax
| cst1 k a => return k.tmgenJax s!"({(← a.codegenJax')})"
| cst2 k a b => return k.tmgenJax s!"({← a.codegenJax'})" s!"({← b.codegenJax'})"
| abs f (β:=β) => do
  let v := (←VParM.parVPar) _
  let s := s!"(lambda {v}: {←(f v).codegenJax'})"
  return s
  -- return if β.containsUnsupported then s else s!"jit{s}"
| bld (n:=n) (α:=α) f => do
  let v := (←VParM.parVPar) _
  if α.containsUnsupported
    then return s!"[(lambda {v}: {←(f v).codegenJax'})({v}) for {v} in range(0,{n})]"
    else return s!"(jax.vmap(lambda {v}: {←(f v).codegenJax'})(jnp.arange({n})))"
| bnd e f => do
  let v := (←VParM.parVPar) _
  return s!"(lambda {v}={←e.codegenJax'}: \n{←(f v).codegenJax'})()"
| ite cond a b (β:=β) =>
  if β.containsUnsupported
  then return s!"({<- a.codegenJax'} if {<- cond.codegenJax'} else {<- b.codegenJax'})"
  else return s!"(lax.cond({← cond.codegenJax'}, lambda: {<- a.codegenJax'}, lambda: {<- b.codegenJax'}))"

-- generates a python expression
def Tm.codegenJax (t: Tm VPar α): String := Tm.codegenJax' t |>.startZero

instance genJax: Codegen "Jax" :=
  ⟨(s!"print(to_py({Tm.codegenJax ·}))")⟩

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
