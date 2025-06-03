import Polara.Optimizations.NbE
import Polara.Optimizations.CSE
import Polara.Syntax.Index

open Prim

-- Env wo wir sind mit wo wir variable benutzen wollen vergleichen
def Env.withargsJax (s: String): Env → String
  | .nil       => s
  | .func Γ _α i => s!"{Γ.withargsJax s}({i.pretty})"
  | .forc Γ _n i => s!"({Γ.withargsJax s})[{i.pretty}]"
  | .itec Γ _i _b => s!"{Γ.withargsJax s}"

-- in gemeinsame util?
def Var.tmgenJax (env: Env) (x: Var α): Orig String := do
  let originalAINF <- read
  match x.lookupEnv originalAINF with -- <- Zugriff aufs Orignal
  | some env => return env.withargsJax x.pretty -- variable übergeben
  | none   => return "(" ++ x.pretty ++ " ???)"
def VPar.tmgenJax (Γ: Env) (x: VPar α): Orig String :=
  match x with
  | .v x => x.tmgenJax Γ
  | .p x => return x.pretty

-- zusätzliche Funktion passende "leere" instance

def Env.wrapJax (s: String): Env → Orig String -- neue variable in env definieren gegenteil withargs
| .nil            => return s
| .func Γ _ i     => wrapJax  s!"(lambda {i.pretty}: {s})" Γ
| .forc Γ n i     => wrapJax  s!"jax.vmap(lambda {i.pretty}: {s})(jnp.arange({n}))" Γ
-- tothink no None in jax, NaN only with float abandon ints?
| .itec Γ cond true  => do
    let cond' <- cond.tmgenJax Γ
    wrapJax  s!"({s} if {cond'} != 0 else None)" Γ
| .itec Γ cond false => do
    let cond' <- cond.tmgenJax Γ
    wrapJax  s!"({s} if {cond'} == 0 else None)" Γ
-- | .itec Γ cond true  => do
--     let cond' <- cond.tmgenJax Γ
--     wrapJax  s!"({s} if {cond'} != 0 else None)" Γ
-- | .itec Γ cond false => do
--     let cond' <- cond.tmgenJax Γ
--     wrapJax  s!"({s} if {cond'} == 0 else None)" Γ

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
  | sum => "jnp.sum"            ++ s!"({a})"

def Const2.tmgenJax (a: String) (b: String): Const2 α₁ α₂ α → String
  | addn => s!"{a} + {b}" | muln => s!"{a} * {b}"
  | addf => s!"{a} + {b}" | subf => s!"{a} - {b}"
  | mulf => s!"{a} * {b}" | divf => s!"{a} / {b}"
  | maxf => s!"max({a}, {b})"
  | addi => s!"{a} + {b}"
  | tup  => s!"({a}, {b})"
  | app  => s!"{a}({b})"
  | get  => s!"{a}[{b}]"

def Prim.tmgenJax (Γ: Env): Prim α → Orig String
| err => return "None"
| cst0 k => return k.tmgenJax
| cst1 k a => return k.tmgenJax (<- a.tmgenJax Γ)
| cst2 k a b => return k.tmgenJax (<- a.tmgenJax Γ) (<- b.tmgenJax Γ)
| var i => return i.pretty
| abs (α:=_γ) i e => do
  let e' <- e.tmgenJax (.func Γ _ i)
  return s!"(lambda {i.pretty}: {e'})"
| bld (n:=n) i v => do
    let v' <- v.tmgenJax (.forc Γ n i)
    return s!"(jax.vmap(lambda {i.pretty}: {v'})(jnp.arange({n})))"
| .ite cond a b => do
    let cond' <- cond.tmgenJax Γ
    let a' <- a.tmgenJax (.itec Γ cond true)
    let b' <- b.tmgenJax (.itec Γ cond false)
    return s!"({a'} if {cond'} != 0 else {b'})"
    -- return s!"(lax.cond({cond'} != 0, lambda: {a'}, lambda: {b'}))"

def codegenRecJax (k: String → String): AINF α → Orig String
| .ret x => return k x.pretty
| .bnd (α:=_β) Γ v prim rest => return (
  s!"{v.pretty} = {<- Γ.wrapJax  (<- prim.tmgenJax Γ)}\n"
  ++ (<- codegenRecJax k rest)
)

-- k - kontinuation z.B. return x für letzte zeile oder zusammenfügen mehrerer
-- use k for jit?
def AINF.codegenJax (k: String → String) (a: AINF α): String :=
  codegenRecJax k a a
