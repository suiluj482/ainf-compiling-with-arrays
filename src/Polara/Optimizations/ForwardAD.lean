import Polara.Syntax.Index
import Polara.Optimizations.NbE
import Polara.Optimizations.CSE

@[reducible]
def Ty.linArg: Ty → Ty
| .unit
| .nat
| .idx _
| .lin       => .unit
| α ×× β     => α.linArg ×× β.linArg
| .array n α => .array n α.linArg
| .ref _     => panic! "ref not supported in automatic differentiation"
| .flt       => .lin
| α ~> β     => α ~> β.linArg

@[reducible]
def Ty.linRet := Ty.linArg

@[reducible]
def Ty.linFun: Ty → Ty → Ty
| α, β => α.linArg ~> β.linRet

mutual
  @[reducible]
  def Ty.df': Ty → Ty
  | .unit      => .unit
  | .nat       => .nat
  | .flt       => .flt
  | .idx n     => .idx n
  | α ×× β     => α.df' ×× β.df'
  | .array n α => .array n α.df'
  | .lin       => .lin
  | .ref _     => panic! "ref not supported in automatic differentiation"
  | α ~> β     => α.df ~> β.df'

  @[reducible]
  def Ty.df: Ty → Ty
  | .unit      => .unit
  | .nat       => .nat
  | .flt       => .flt
  | .idx n     => .idx n
  | α ~> β     => α.df ~> (β.df ×× (Ty.linFun α.df' β.df'))
  | α ×× β     => α.df ×× β.df
  | .array n α => .array n α.df
  | .lin       => .lin
  | .ref _     => panic! "ref not supported in automatic differentiation"
end

@[reducible]
def EnvDf := List (Some VPar)
@[reducible]
def EnvDf.ty: EnvDf → Ty
| [] => .unit
| ⟨α,_⟩ :: env' => α ×× EnvDf.ty env'
@[reducible]
def Ty.dfEnv (env: EnvDf): Ty → Ty
| α => (α.df ×× (Ty.linFun (EnvDf.ty env).df' α.df'))

-- open Ty in
-- #eval flt ~> flt |>.df
-- open Ty in
-- #eval flt ~> flt ~> flt |>.df


------------------------------------------------------------------------------------------
-- except Const2.app functions only changing type
----

def Const0.df: Const0 α → Tm Γ α.df
| .litn n => tlitn n
| .litf f => tlitf f
| .liti i => tliti i
| .litl l => tlitl l
| .litu => tlitu
| mkRef => panic! "ref not supported in automatic differentiation"

def Const1.df (x: Tm Γ α.df): Const1 α β → Tm Γ β.df
| .exp     => Tm.cst1 Const1.exp x
| .sqrt    => Tm.cst1 Const1.sqrt x
| .normCdf => Tm.cst1 Const1.normCdf x
| .log     => Tm.cst1 Const1.log x
| .fst     => Tm.cst1 Const1.fst x
| .snd     => Tm.cst1 Const1.snd x
| .sumf    => Tm.cst1 Const1.sumf x
| .suml    => Tm.cst1 Const1.suml x
| .i2n     => Tm.cst1 Const1.i2n x
| .n2f     => Tm.cst1 Const1.n2f x
| refGet => panic! "ref not supported in automatic differentiation"

def ArithOp.df [t: BiArraysC BiArith α β γ](op: ArithOp)
  (a: Tm Γ α.df)(b: Tm Γ β.df): Tm Γ γ.df :=
   match t.t with
  | .array n t' =>
      have: BiArraysC BiArith _ _ _ := ⟨t'⟩
      for' i => (ArithOp.df op a[[i]] b[[i]])
  | .base t' => match t' with
    | .nats => Tm.cst2 (.arithOp op) a b
    | .flts => Tm.cst2 (.arithOp op) a b
def linOpDf [t: BiArraysC BiLin α β γ](op: AddOp)
  (a: Tm Γ α.df)(b: Tm Γ β.df): Tm Γ γ.df :=
  match t.t with
  | .array n t' =>
      have: BiArraysC BiLin _ _ _ := ⟨t'⟩
      for' i => (linOpDf op a[[i]] b[[i]])
  | .base t' => match t' with
    | .lins => Tm.cst2 (.linOp op) a b
def linScaleDf [t: BiArrayC BiLF α β γ](op: MulOp)
  (a: Tm Γ α.df)(b: Tm Γ β.df): Tm Γ γ.df :=
  let go {α' β' γ'}[t: BiLFC α' β' γ'](a: Tm Γ α'.df)(b: Tm Γ β'.df): Tm Γ γ'.df :=
    match t.t with
    | .lf => (Tm.cst2 (.linScale op) a b)

  match t.t with
  | .array n t' =>
      have: BiLFC _ _ _ := ⟨t'⟩
      for' i => (go a[[i]] b[[i]])
  | .base t' =>
      have: BiLFC _ _ _ := ⟨t'⟩
      go a b

def Const2.df (a: Tm Γ α.df)(b: Tm Γ β.df): Const2 α β γ → Tm Γ γ.df
| arithOp op => op.df a b
| linOp op => linOpDf op a b
| linScale op => linScaleDf op a b
| .addi => Tm.cst2 (.addi) a b
| .lt => a <' b
| .maxf => Max.max a b
| .get  => a[[b]]
| .tup  => (a,, b)
| .refSet => panic! "refSet not supported in automatic differentiation"
| .app  => (a @@ b).fst -- derivation no longer needed


-----------------------------------------------------------------------------------------
-- derivation rules
----

def Const0.df': Const0 α → Tm Γ α.df'.linRet
| .litn n | .liti i | .litl l | .litu => ()'
| mkRef => panic! "ref not supported in automatic differentiation"
| .litf f => tlitl 0

def Const1.df' (x: Tm Γ α.df)(x': Tm Γ α.df'.linRet):
  Const1 α β → Tm Γ β.df'.linRet
| .exp     => x' * x.exp               -- (e^x)' = e^x
| .sqrt    => x' / (tlitf 2 * x.sqrt)  -- (sqrt x)' = 1/(2*sqrt x)
| .normCdf =>                          -- (normCdf x)' = (1/sqrt(2*pi)) * e^(-x^2/2) * dx
    (x' / (tlitf 2 * Tm.π).sqrt) * (tlitf 0 - (x * x / (tlitf 2))).exp
| .log     => x' / x                   -- (log x)' = 1/x
| .fst     => x'.fst
| .snd     => x'.snd
| .sumf    => x'.suml
| .suml    => ()'
| .i2n     => ()'
| .n2f     => tlitl 0
| refGet => panic! "ref not supported in automatic differentiation"

def ArithOp.df' [t: BiArraysC BiArith α β γ](op: ArithOp)
  (a: Tm Γ α.df)(b: Tm Γ β.df)(a': Tm Γ α.df'.linRet)(b': Tm Γ β.df'.linRet): Tm Γ γ.df'.linRet :=
   match t.t with
  | .array n t' =>
      have: BiArraysC BiArith _ _ _ := ⟨t'⟩
      for' i => (ArithOp.df' op a[[i]] b[[i]] a'[[i]] b'[[i]])
  | .base t' => match t' with
    | .nats => ()'
    | .flts =>
        match op with
        | .add => a' + b'                     -- (a + b)' = a' + b'
        | .sub => a' - b'                     -- (a - b)' = a' - b'
        | .mul => b' * a + a' * b             -- (a * b)' = a' * b + a * b'
        | .div => (a' * b - b' * a) / (b * b) -- (a / b)' = (a' * b - a * b') / (b^2)
def linOpDf' [t: BiArraysC BiLin α β γ]: Tm Γ γ.df'.linRet :=
  match t.t with
  | .array n t' => for' i => @linOpDf' _ _ _ _ ⟨t'⟩
  | .base (.lins) => ()'
def linScaleDf' [t: BiArrayC BiLF α β γ]: Tm Γ γ.df'.linRet :=
  match t.t with
  | .array n (.lf) => for' i => ()'
  | .base (.lf) => ()'

def Const2.df' (a: Tm Γ α.df)(b: Tm Γ β.df)(a': Tm Γ α.df'.linRet)(b': Tm Γ β.df'.linRet): Const2 α β γ → Tm Γ γ.df'.linRet
| arithOp op  => op.df' a b a' b'
| linOp op    => @linOpDf' α β _ _ _
| linScale op => @linScaleDf' α β _ _ _
| .addi       => ()'
| .lt         => ()'
| .maxf       => if' a <' b then a' else b'
| .get        => a'[[b]]
| .tup        => (a',, b')
| .refSet     => panic! "refSet not supported in automatic differentiation"
| .app        => (a @@ b).snd @@ b'


----------------------------------------------------------------------------------------------

def VPar.dfEnv (env: EnvDf): VPar α → VPar (α.dfEnv env) := VPar.changeType
def VPar.idfEnv (env: EnvDf): VPar (α.dfEnv env) → VPar α := VPar.changeType

def VPar.df: VPar α → VPar α.df := VPar.changeType
def VPar.idf: VPar α.df → VPar α := VPar.changeType

def Tm.linZero (α: Ty): Tm Γ α :=
  match α with
  | .lin => Tm.cst0 (Const0.litl 0)
  | _ ~> β => Tm.abs (λ _ => Tm.linZero β)
  | α ×× β => Tm.cst2 Const2.tup (Tm.linZero α) (Tm.linZero β)
  | .array _ α => Tm.bld (λ _ => Tm.linZero α)
  | .unit => ()'
  | .nat | .idx _ | .flt => panic! "Tm.linZero does not support this type"
  | .ref _ => panic! "Tm.linZero does not support references"

def Tm.df'(env: EnvDf): Tm VPar α → Tm VPar (α.dfEnv env)
| .err => (.err,, fun' e => .err)
| .cst0 const0        => (
      const0.df,,
      fun' e => const0.df'
    )
| .cst1 const1 t      =>
    let' t := t.df' env;
    (
      const1.df t.fst,,
      fun' e => const1.df' t.fst (t.snd @@ e)
    )
| .cst2 const2 a b    =>
    let' a := a.df' env;
    let' b := b.df' env;
    (
      const2.df a.fst b.fst,,
      fun' e => const2.df' a.fst b.fst (a.snd @@ e) (b.snd @@ e)
    )
| .bld a              =>
  let' arr := for'v idx => (a idx).df' env;
  (
    for' idx => arr[[idx]].fst,,
    fun' e => for' idx => (arr[[idx]].snd @@ e)
  )
| .ite cond a b       => .ite cond (a.df' env) (b.df' env)
| .var v (α:=α)       =>
    let rec go (env': EnvDf)(f: Tm VPar env.ty.df'.linArg → Tm VPar (env'.ty.df'.linArg)):
      Tm VPar (α.dfEnv env) :=
        match env' with
        | [] => .var (v.dfEnv env) -- VPar not in env therefore allready changed by Tm.df'
        | ⟨α',x⟩ :: env'' => if t: α=α' then if x=t▸v
            then (.var v.df,, fun' e => t▸(f e).fst) -- in env, get df from env
            else go env'' (Tm.snd ∘ f) else go env'' (Tm.snd ∘ f)
    go env id
| .bnd t f            => let'v v := t.df' env; (f (v.idfEnv env)).df' env
| .abs f              =>
    let' f := fun'v x => (f x.idf).df' (⟨_,x.idf⟩ :: env);
    (
      fun' x =>
        let' body := f @@ x;
        (
          body.fst,,
          fun' x' => body.snd @@ (x',, Tm.linZero _)
        ),,
      fun' e => fun' x =>
        let' body := f @@ x;
        body.snd @@ (Tm.linZero _,, e)
    )

def Tm.df (t: Tm VPar α): Tm VPar α.df :=
  t.df' [] |>.fst -- remove derivation of empty env


------------------------------------------------
-- open Ty

-- #eval (fun' x:flt => x.exp).df |>.normVPar

-- #eval flt |>dfEnv [⟨flt, (.v (.mk 1))⟩]
-- #eval flt ~> flt |>.dfEnv []
-- #eval flt ~> flt ~> flt |>.dfEnv []
