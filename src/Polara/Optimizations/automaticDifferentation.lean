import Polara.Syntax.Index
import Polara.Optimizations.NbE

@[reducible]
def Ty.aD: Ty → Ty
| .nat => .nat
| .flt => .flt ×× .flt
| .idx n => .idx n
| α ~> β => α.aD ~> β.aD
| α ×× β => α.aD ×× β.aD
| .array n α => .array n α.aD

#reduce Ty.nat.aD
#reduce Ty.flt.aD
#reduce Ty.flt ~> Ty.flt |>.aD
#reduce Ty.flt ~> Ty.flt ~> Ty.flt |>.aD

-- f : flt → flt
-- f' : flt → flt
-- [f] : flt × flt → fl × flt
-- [f] (x, dx) := (f x, f x + dx * f' x)

def Const0.aD: Const0 α → Tm Γ α.aD
| .litn n => tlitn n
| .litf f => tupple' (tlitf f) (tlitf 0)
| .liti i => tliti i

private def helperAD (x x': Tm Γ Ty.flt): Tm Γ (Ty.flt ×× Ty.flt) :=
  tupple' x (x + x')

def Const1.aD (x: Tm Γ α.aD): Const1 α β → Tm Γ β.aD
| .exp     => helperAD x.fst.exp     (x.snd * x.fst.exp) -- (e^x)' = e^x
| .sqrt    => helperAD x.fst.sqrt    (x.snd / (@tlitf Γ 2 * x.fst.sqrt)) -- (sqrt x)' = 1/(2*sqrt x)
| .normCdf => helperAD x.fst.normCdf
    (
      let π := @tlitf Γ 3.14159265358979323846
      (tlitf 2 / π.sqrt) *
      Tm.exp (tlitf 0 - (x.fst * x.fst / (tlitf 2)))
    ) -- (normCdf x)' = (1/sqrt(2*pi)) * e^(-x^2/2) * dx
| .log     => helperAD x.fst.log     (x.snd / x.fst) -- (log x)' = 1/x
| .fst     => x.fst
| .snd     => x.snd
| .sumf    => helperAD -- (sum x)' = sum (x')
    (for' i => x[[(i)]].fst).sumf
    (for' i => x[[(i)]].snd).sumf
| .i2n     => x.i2n
| .n2f     => tupple' x.n2f (tlitf 0)

def ArithOp.aD [t: TypeArithOp α β γ](op: ArithOp)
  (a: Tm Γ α.aD)(b: Tm Γ β.aD): Tm Γ γ.aD :=
   match t.type with
  | .nats => Tm.cst2 (.arithOp op) a b
  | .flts => helperAD
      (Tm.cst2 (.arithOp op) a.fst b.fst)
      (
        match op with
        | .add => a.snd + b.snd -- (a + b)' = a' + b'
        | .sub => a.snd - b.snd -- (a - b)' = a' - b'
        | .mul => a.fst * b.snd + a.snd * b.fst -- (a * b)' = a' * b + a * b'
        | .div => (a.snd * b.fst - a.fst * b.snd) / (b.fst * b.fst) -- (a / b)' = (a' * b - a * b') / (b^2)
      )
  | .elementsArray n t' =>
      have: TypeArithOp _ _ _ := ⟨t'⟩
      for' i => (ArithOp.aD op a[[i]] b[[i]])

def Const2.aD (a: Tm Γ α.aD)(b: Tm Γ β.aD): Const2 α β γ → Tm Γ γ.aD
| arithOp op => op.aD a b
| .addi => Tm.cst2 (.addi) a b
| .maxf => helperAD
    (Tm.cst2 (.maxf) a.fst b.fst)
    (if' Tm.err then a.snd else b.snd) -- what if a=b?
| .get  => Tm.cst2 (.get)  a b
| .tup  => Tm.cst2 (.tup)  a b
| .app  => Tm.cst2 (.app)  a b

def VPar.changeType: VPar α → VPar β
| .v (.mk n) => .v (.mk n)
| .p (.mk n) => .p (.mk n)
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

-- #eval (fun' i: Ty.flt => i + tlitf 2).aD.normVPar
