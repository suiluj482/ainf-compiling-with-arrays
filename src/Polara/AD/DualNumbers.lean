import Polara.Syntax.All
import Polara.Optimizations.NbE
import Polara.Optimizations.CSE

@[reducible]
def Ty.aD: Ty → Ty :=
  Ty.transform (λ
    |.flt => .flt ×× .lin
    | α => α
  )
-- | .lin => .lin -- todo


-- f: flt ×× lin ×× flt ×× lin ~> flt ×× lin
-- f(x, 0, y, 1): (z, f' x y)

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
| .litf f => (tlitf f,, tlitl 0) -- selector, gewicht der Ableitungsrichtung
| .liti i => tliti i
| .litl l => tlitl l
| .litu => tlitu
| mkRef => panic! "ref not supported in automatic differentiation"

def Const1.aD (x: Tm Γ α.aD): Const1 α β → Tm Γ β.aD
| .exp     => (x.fst.exp ,, x.snd * x.fst.exp)              -- (e^x)'    = e^x
| .log     => (x.fst.log,,  x.snd / x.fst)                  -- (log x)'  = 1/x
| .sqrt    => (x.fst.sqrt,, x.snd / (tlitf 2 * x.fst.sqrt)) -- (sqrt x)' = 1/(2*sqrt x)
| .normCdf => (x.fst.normCdf,, -- (normCdf x)' = (1/sqrt(2*pi)) * e^(-x^2/2) * dx
      x.snd * (tlitf 1 / (tlitf 2 * Tm.π).sqrt *
      (tlitf 0 - x.fst * x.fst / tlitf 2).exp)
    )
| .fst     => x.fst
| .snd     => x.snd
| .sumf    => ( -- (sum x)' = sum (x')
      (for' i => x[[(i)]].fst).sumf,,
      (for' i => x[[(i)]].snd).suml
    )
| .suml    => x.suml
| .i2n     => x.i2n
| .n2f     => (x.n2f,, tlitl 0)
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
          | .add => -- (a + b)' = a' + b'
              a.snd + b.snd
          | .sub => -- (a - b)' = a' - b'
              a.snd - b.snd
          | .mul => -- (a * b)' = a' * b + a * b'
              b.snd * a.fst + a.snd * b.fst
          | .div => -- (a / b)' = (a' * b - a * b') / (b^2)
             (a.snd * b.fst - b.snd * a.fst) / (b.fst * b.fst)
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
| .eqi  => Tm.cst2 (.eqi) a b
| .lt => a.fst <' b.fst
| .maxf => (a.fst.maxf b.fst,,
    (if' a.fst <' b.fst then b.snd else a.snd)
  )
| .get  => a[[b]]
| .tup  => (a,, b)
| .app  => a @@ b
| .refSet => panic! "refSet not supported in automatic differentiation"

def VPar.aD:  VPar α    → VPar α.aD := VPar.changeType
def VPar.iaD: VPar α.aD → VPar α    := VPar.changeType

def Tm.aD: Tm VPar α → Tm VPar α.aD
| .err => .err
| .cst0 const0 => const0.aD
| .cst1 const1 t => const1.aD t.aD
| .cst2 const2 a b => const2.aD a.aD b.aD
| .abs f => fun'v x   => (f x.iaD).aD
| .bld a => for'v idx => (a idx).aD
| .ite cond a b => if' cond then a.aD else b.aD
| .var v => .var v.aD
| .bnd rest l => let'v v := rest.aD; (l v.iaD).aD

-- #eval (fun' j: Ty.flt => for'v i:10 => (Tm.n2f (Tm.i2n (Tm.var i))) + j).aD.normVPar
-- #eval (fun' i: Ty.flt => fun' j: Ty.flt => i + j).aD.normVPar.toAINF

-- direkt auf ainf und getrennten ainf generieren? how to map params in val to params in ad?
