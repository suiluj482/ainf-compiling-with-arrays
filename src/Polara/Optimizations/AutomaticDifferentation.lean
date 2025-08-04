import Polara.Syntax.Index
import Polara.Optimizations.NbE
import Polara.Optimizations.CSE

-- @[reducible]
-- def Ty.aD': Ty → Option Ty
-- | .unit
-- | .idx _
-- | .ref _
-- | .lin
-- | .nat => none
-- | .flt => lin
-- | .array n α => α.aD'.map (.array n ·)
-- | α ×× β => α.aD'.merge (·××·) β.aD'
-- | α ~> β => α.aD'.merge (·~>·) β.aD'

-- -- #eval Ty.contains
-- @[reducible]
-- def Ty.containsFunc := (Ty.contains · (λ
--   | _ ~> _ => true
--   | _ => false
--   ))

-- def Ty.aD (l: Option Ty): Ty → Ty
-- | α ~> β => α.aD (none) ~> β.aD (α.aD')
-- | _ => sorry

-- -- flt ~> flt     |>.aD flt ~> (flt ×× (lin ~> lin))
-- -- flt ~> (flt ×× nat) |>.aD flt ~> ((flt ×× nat) ×× (lin ~> lin))
-- -- flt ~> (flt ~> flt) |>.aD flt ~> (flt ~> (flt ×× (lin ~> lin ~> lin)))

-- -- flt ~> (flt ×× (flt ~> flt)) |>.aD flt ~> (flt ×× ((flt ~> flt) ×× (lin ~> lin ~> lin))) ×× (lin ~> lin)
-- -- alternatively (lin ~> (lin ×× (lin ~> lin)) but we need info from not lin part

-- def Ty.aD (l: Option Ty): Ty → Ty
-- | .unit => l.map (.unit ×× ·) |>.getD .unit
-- | .idx n => l.map (.idx n ×× ·) |>.getD .idx n
-- | .lin => l.map (.lin ×× ·) |>.getD .lin
-- | .nat => l.map (.nat ×× ·) |>.getD .nat
-- | .flt =>
-- | .ref α =>
-- | .array n α => α.aD'.map (.array n ·)
-- | α ×× β => α.aD'.merge (·××·) β.aD'
-- | α ~> β => α.aD'.merge (·~>·) β.aD'
-- | _ => sorry

@[reducible]
def Ty.aD: Ty → Ty
| .unit => .unit
| .nat => .nat
| .flt => .flt ×× .lin
| .idx n => .idx n
| α ~> β => α.aD ~> β.aD
| α ×× β => α.aD ×× β.aD
| .array n α => .array n α.aD
| .ref α => .ref α.aD
| .lin => .lin -- todo

-- #reduce Ty.nat.aD
-- #reduce Ty.flt.aD
-- #reduce Ty.flt ~> Ty.flt |>.aD
-- #reduce Ty.flt ~> Ty.flt ~> Ty.flt |>.aD

-- f : flt → flt
-- f' : flt → flt
-- [f] : flt × flt → fl × flt
-- [f] (x, dx) := (f x, dx * f' x)

def Const0.aD: Const0 α → Tm Γ α.aD
| .litn n => tlitn n
| .litf f => tupple' (tlitf f) (tlitl 0)
| .liti i => tliti i
| .litl l => (tlitl l)
| .litu => tlitu
| mkRef => panic! "ref not supported in automatic differentiation"

def Const1.aD (x: Tm Γ α.aD): Const1 α β → Tm Γ β.aD
| .exp     => tupple' x.fst.exp     (x.snd * x.fst.exp) -- (e^x)' = e^x
| .sqrt    => tupple' x.fst.sqrt    (x.snd / (@tlitf Γ 2 * x.fst.sqrt)) -- (sqrt x)' = 1/(2*sqrt x)
| .normCdf => tupple' x.fst.normCdf
    (
      let π := @tlitf Γ 3.14159265358979323846
      x.snd * (tlitf 2 / π.sqrt) *
      Tm.exp (tlitf 0 - (x.fst * x.fst / (tlitf 2)))
    ) -- (normCdf x)' = (1/sqrt(2*pi)) * e^(-x^2/2) * dx
| .log     => tupple' x.fst.log     (x.snd / x.fst) -- (log x)' = 1/x
| .fst     => x.fst
| .snd     => x.snd
| .sumf    => tupple' -- (sum x)' = sum (x')
    (for' i => x[[(i)]].fst).sumf
    (for' i => x[[(i)]].snd).suml
| .suml    => x.suml
| .i2n     => x.i2n
| .n2f     => tupple' x.n2f (tlitl 0)
| refGet => panic! "ref not supported in automatic differentiation"

def ArithOp.aD [t: BiArraysC BiArith α β γ](op: ArithOp)
  (a: Tm Γ α.aD)(b: Tm Γ β.aD): Tm Γ γ.aD :=
   match t.t with
  | .array n t' =>
      have: BiArraysC BiArith _ _ _ := ⟨t'⟩
      for' i => (ArithOp.aD op a[[i]] b[[i]])
  | .base t' => match t' with
    | .nats => Tm.cst2 (.arithOp op) a b
    | .flts => tupple'
        (Tm.cst2 (.arithOp op) a.fst b.fst)
        (
          match op with
          | .add => a.snd + b.snd -- (a + b)' = a' + b'
          | .sub => a.snd - b.snd -- (a - b)' = a' - b'
          | .mul => b.snd * a.fst + a.snd * b.fst -- (a * b)' = a' * b + a * b'
          | .div => (a.snd * b.fst - b.snd * a.fst) / (b.fst * b.fst) -- (a / b)' = (a' * b - a * b') / (b^2)
        )
def linOpAD [t: BiArraysC BiLin α β γ](op: AddOp)
  (a: Tm Γ α.aD)(b: Tm Γ β.aD): Tm Γ γ.aD :=
  match t.t with
  | .array n t' =>
      have: BiArraysC BiLin _ _ _ := ⟨t'⟩
      for' i => (linOpAD op a[[i]] b[[i]])
  | .base t' => match t' with
    | .lins => Tm.cst2 (.linOp op) a b
def linScaleAD [t: BiArrayC BiLF α β γ](op: MulOp)
  (a: Tm Γ α.aD)(b: Tm Γ β.aD): Tm Γ γ.aD :=
  let go {α' β' γ'}[t: BiLFC α' β' γ'](a: Tm Γ α'.aD)(b: Tm Γ β'.aD): Tm Γ γ'.aD :=
    match t.t with
    | .lf => (Tm.cst2 (.linScale op) a b.fst)

  match t.t with
  | .array n t' =>
      have: BiLFC _ _ _ := ⟨t'⟩
      for' i => (go a[[i]] b[[i]])
  | .base t' =>
      have: BiLFC _ _ _ := ⟨t'⟩
      go a b

def Const2.aD (a: Tm Γ α.aD)(b: Tm Γ β.aD): Const2 α β γ → Tm Γ γ.aD
| arithOp op => op.aD a b
| linOp op => linOpAD op a b
| linScale op => linScaleAD op a b
| .addi => Tm.cst2 (.addi) a b
| .lt => a.fst <' b.fst
| .maxf => tupple'
    (Tm.cst2 (.maxf) a.fst b.fst)
    (if' a.fst <' b.fst then a.snd else b.snd)
| .get  => Tm.cst2 (.get)  a b
| .tup  => Tm.cst2 (.tup)  a b
| .app  => Tm.cst2 (.app)  a b
| .refSet => panic! "refSet not supported in automatic differentiation"

def VPar.aD: VPar α → VPar α.aD := VPar.changeType
def VPar.iaD: VPar α.aD → VPar α := VPar.changeType

def Tm.aD: Tm VPar α → Tm VPar α.aD
| .err => .err
| .cst0 const0 => const0.aD
| .cst1 const1 t => const1.aD t.aD
| .cst2 const2 a b => const2.aD a.aD b.aD
| .abs f => .abs (λ x => (f x.iaD).aD)
| .bld a => .bld (λ idx => (a idx).aD)
| .ite cond a b => .ite cond a.aD b.aD
| .var v => .var v.aD
| .bnd rest l => .bnd rest.aD (λ v => (l v.iaD).aD)

-- #eval (fun' j: Ty.flt => for'v i:10 => (Tm.n2f (Tm.i2n (Tm.var i))) + j).aD.normVPar
-- #eval (fun' i: Ty.flt => fun' j: Ty.flt => i + j).aD.normVPar.toAINF

-- direkt auf ainf und getrennten ainf generieren? how to map params in val to params in ad?
