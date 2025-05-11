import Polara.NbE
import Polara.CSE
import Polara.Syntax.Index
-- import Polara.Examples.Definitions

open Prim

-- def Ty.genPy: Ty → String
--   | flt  => "float"
--   | nat  => "int" -- todo forbid negative?, allow arbitrary large? python not necessarly like lean, efficientcy
--   | idx _ => s!"int"
--   | a~>b => s!"({a.genPy} → {b.genPy}" -- ? Callable?
--   | a××b => s!"(tupel[{a.genPy}, {b.genPy}])"
--   | array _n b => s!"(list[{b.genPy}])" -- todo jax

-- -- todo
-- def Env.tygenPy: String → Env → String
--   | s, .nil        => s
--   | s, .func Γ α _i => Γ.tygenPy s!"({α.genPy} → Except String {s})"
--   | s, .forc Γ _n _i => Γ.tygenPy s!"(Array {s})"
--   | s, .itec Γ _i _m => Γ.tygenPy s!"(Except String {s})"

-- namespace Python
-- open Python

-- JAX
--  jax array, primitive in 1 dim array, alles ist ein array
--  ite jax.cond, jax.vmap, .range?

def Env.withargsPy (s: String): Env → String -- Env wo wir sind mit wo wir variable benutzen wollen vergleichen
  | .nil       => s
  | .func Γ _α i => s!"{Γ.withargsPy s}({i.pretty})"
  | .forc Γ _n i => s!"({Γ.withargsPy s})[{i.pretty}]"
  | .itec Γ _i _b => s!"{Γ.withargsPy s}"

-- in gemeinsame util?
def Var.tmgenPy (Γ: Env) (x: Var α): Orig String := do
  match lookupEnv x (<- read) with -- <- Zugriff aufs Orignal
  | some Δ => return Δ.withargsPy x.pretty -- variable übergeben
  | none   => return "(" ++ x.pretty ++ " ???)"
def VPar.tmgenPy (Γ: Env) (x: VPar α): Orig String :=
  match x with
  | .v x => x.tmgenPy Γ
  | .p x => return x.pretty

def Env.wrapPy (s: String): Env → Orig String -- neue variable in env definieren gegenteil withargs
| .nil            => return s
| .func Γ _ i     => wrapPy  s!"(lambda {i.pretty}: {s})" Γ
| .forc Γ n i     => wrapPy  s!"[{s} for {i.pretty} in range(0,{n})]" Γ
| .itec Γ i true  => do wrapPy  s!"({s} if {<- i.tmgenPy Γ} != 0 else None)" Γ
| .itec Γ i false => do wrapPy  s!"({s} if {<- i.tmgenPy Γ} == 0 else None)" Γ

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
  | sum => "sum"                ++ s!"({a})"

def Const2.tmgenPy (a: String) (b: String): Const2 α₁ α₂ α → String
  | addn => s!"{a} + {b}" | muln => s!"{a} * {b}"
  | addf => s!"{a} + {b}" | subf => s!"{a} - {b}" | mulf => s!"{a} * {b}" | divf => s!"{a} / {b}" | maxf => s!"max({a}, {b})"
  | addi => s!"{a} + {b}"
  | tup  => s!"({a}, {b})"
  | app  => s!"{a}({b})"
  | get  => s!"{a}[{b}]!"

def Prim.tmgenPy (Γ: Env): Prim α → Orig String
| err => return "ERROR"
| cst0 k => return k.tmgenPy
| cst1 k a => return k.tmgenPy (<- a.tmgenPy Γ)
| cst2 k a b => return k.tmgenPy (<- a.tmgenPy Γ) (<- b.tmgenPy Γ)
| var i => return i.pretty
| abs (α:=γ) i e => return s!"(lambda {i.pretty}: {<- e.tmgenPy (.func Γ _ i)})"
| bld (n:=n) i e => return  s!"[{<- e.tmgenPy (.forc Γ n i)} for {i.pretty} in range(0,{n})]"
| .ite a b c => return s!"({<- b.tmgenPy (.itec Γ a true )} if {<- a.tmgenPy Γ} != 0 else {<- c.tmgenPy (.itec Γ a false)})"

def codegenRecPy (k: String → String): AINF α → Orig String
| .ret x => return k x.pretty
| .bnd (α:=β) Γ xᵢ prim rest => return (
  s!"{xᵢ.pretty} = {<- Γ.wrapPy  (<- prim.tmgenPy Γ)}\n"
  ++ (<- codegenRecPy k rest)
)

def AINF.codegenPy (k: String → String) (a: AINF α): String :=
  codegenRecPy k a a -- kontinuation z.B. return x für letzte zeile oder zusammenfügen mehrerer


---------Tests---------------------------
-- open Tm Ty Const0 Const1 Const2
-- def cseTest1 {Γ : Ty → Type} : Tm Γ (Ty.nat ~> Ty.nat) :=
--   fun' x => -- 1+x should be shared across the branches
--     if' (var x)
--       then tlitn 42 + (tlitn 1 + var x)
--       else tlitn 24 + (tlitn 1 + var x)
-- def cseTest1AINF := cseTest1.toAINF
-- def cseTest1CSE := cseTest1.toAINF.cse [] []

-- -- def test: Term nat := (tlitn 1) - (tlitn 20)

-- #eval cseTest1.pretty |>.toFormat
-- #eval cseTest1CSE
-- #eval cseTest1CSE.codegenPy (s!"print({·})") |>.toFormat



-- def testPolara: Tm Γ (Ty.nat) := Tm.cst0 (Const0.litn 1)
-- #eval testPolara.pp (0, 0)
-- def testAINF := testPolara.toAINF.cse [] []
-- #eval testAINF.pretty id
-- def testPy := testAINF.codegenPy (s!"print({·})")
-- #eval testPy
