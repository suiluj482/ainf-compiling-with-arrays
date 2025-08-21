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
def Ty.linFun: Ty → Ty := Ty.linArg

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
  | α ~> β     => α.df ~> (β.df ×× (α.df'.linArg ~> β.df'.linFun))
  | α ×× β     => α.df ×× β.df
  | .array n α => .array n α.df
  | .lin       => .lin
  | .ref _     => panic! "ref not supported in automatic differentiation"
end

-- open Ty in
-- #eval flt ~> flt |>.df
-- open Ty in
-- #eval flt ~> flt ~> flt |>.df

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


--------------------------------------------------------------------
def Const0.df': Const0 α → Tm Γ α.df'.linFun
| .litn n | .liti i | .litl l | .litu => ()'
| mkRef => panic! "ref not supported in automatic differentiation"
| .litf f => tlitl 0

def Const1.df' (x: Tm Γ α)(x': Tm Γ α.df'.linFun):
  Const1 α β → Tm Γ β.df'.linFun
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
  (a: Tm Γ α)(b: Tm Γ β)(a': Tm Γ α.df'.linFun)(b': Tm Γ β.df'.linFun): Tm Γ γ.df'.linFun :=
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
def linOpDf' [t: BiArraysC BiLin α β γ]: Tm Γ γ.df'.linFun :=
  match t.t with
  | .array n t' => for' i => @linOpDf' _ _ _ _ ⟨t'⟩
  | .base (.lins) => ()'
def linScaleDf' [t: BiArrayC BiLF α β γ]: Tm Γ γ.df'.linFun :=
  match t.t with
  | .array n (.lf) => for' i => ()'
  | .base (.lf) => ()'

def Const2.df' (a: Tm Γ α)(b: Tm Γ β)(a': Tm Γ α.df'.linFun)(b': Tm Γ β.df'.linFun): Const2 α β γ → Tm Γ γ.df'.linFun
| arithOp op  => op.df' a b a' b'
| linOp op    => @linOpDf' α β _ _ _
| linScale op => @linScaleDf' α β _ _ _
| .addi       => ()'
| .lt         => ()'
| .maxf       => if' a <' b then a' else b'
| .get        => a'[[b]]
| .tup        => (a',, b')
| .refSet     => panic! "refSet not supported in automatic differentiation"
| .app        => sorry -- (a' @@ b').snd --

-- def Tm.df' (x': VPar α'): Tm VPar α → Tm VPar α.df'.linFun
-- | .err => .err
-- | .cst0 const0        => const0.df'
-- | .cst1 const1 t      => const1.df' t (t.df' x')
-- | .cst2 const2 a b    => const2.df' a b (a.df' x') (b.df' x')
-- | .bld a              => for'v idx => (a idx).df' x'
-- | .ite cond a b       => .ite cond (a.df' x') (b.df' x')
-- | .var v              => .var v.changeType
-- | .bnd t f            => let'v v := t.df' x'; (f v.changeType).df' x'
-- | .abs f              => fun'v y => (f y.changeType).df' x'

-- def Tm.df: Tm VPar α → Tm VPar α.df
-- | .err => .err
-- | .cst0 const0        => const0.df
-- | .cst1 const1 t      => const1.df t.df
-- | .cst2 const2 a b    => const2.df a.df b.df
-- | .bld a              => for'v idx => (a idx).df
-- | .ite cond a b       => .ite cond a.df b.df
-- | .var v              => .var v.changeType
-- | .bnd t f            => let'v v := t.df; (f v.changeType).df
-- | .abs f              => fun'v x =>
--   let body := f x.changeType
--   (
--     body.df,,
--     fun'v x' => body.df' x'
--   )

def RenDf := ListMap Var (Var) -- x => x', also model type change?, parameters?

def Bnds.df' (ren: RenDf): Bnds → VParM Bnds
| [] => return []
| ⟨⟨_,v⟩, env, prim⟩ :: rest =>
    match prim with
    | .err => sorry
    | _ => sorry

-- renaming
def AINF.df' (ren: RenDf): AINF α → VParM (AINF α.df)
| (bnds, ret) => return (←bnds.df' ren, ret.changeType) -- ren for ret?

def AINF.df: AINF α → AINF α.df
| a => a.df' [] |>.freshAINFVars a
