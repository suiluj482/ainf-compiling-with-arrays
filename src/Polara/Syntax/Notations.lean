import Polara.Syntax.Definitions
import Polara.Syntax.PrettyPrint

open Tm Ty Const0 Const1 ArithOp AddOp MulOp Const2

-- Ty
def Ty.matrix: Nat → Nat → Ty → Ty := (Ty.array · <| Ty.array · ·)
notation:max ty"[["n"]]" => Ty.array n ty
notation:max ty"[["n","m"]]" => Ty.matrix n m ty

-- Tm
notation:max "let' "x" := "term";"res => Tm.bnd term (λ x => let x := Tm.var x; res)
notation:max "let' "x":"α" := "term";"res => @Tm.bnd _ α _ term (λ x => let x := Tm.var x; res)
notation:max "fun' "i" => "term => Tm.abs (λ i => let i := Tm.var i; term)
notation:max "fun' "i":"α" => "term => @Tm.abs _ α _ (λ i => let i := Tm.var i; term)
notation:max "for' "i" => "term => Tm.bld (λ i => let i := Tm.var i; term)
notation:max "for' "i":"n" => "term => @Tm.bld _ n _ (λ i => let i := Tm.var i; term)
notation:max "if' "cond" then "a" else "b => Tm.ite cond a b

notation:max "let'v "x" := "term";"res => Tm.bnd term (λ x => res)
notation:max "fun'v "i" => "term => Tm.abs (λ i => term)
notation:max "fun'v "i":"α" => "term => @Tm.abs _ α _ (λ i => term)
notation:max "for'v "i" => "term => Tm.bld (λ i => term)
notation:max "for'v "i":"n" => "term => @Tm.bld _ n _ (λ i => term)

-- cst0
def tlitu: Tm Γ unit := Tm.cst0 Const0.litu
def tlitn: Nat → Tm Γ nat := Tm.cst0 ∘ Const0.litn
def tlitf: Float → Tm Γ flt := Tm.cst0 ∘ Const0.litf
def tlitl: Float → Tm Γ lin := Tm.cst0 ∘ Const0.litl
def tliti: (Fin (n+1)) → Tm Γ (Ty.idx (n)) := Tm.cst0 ∘ Const0.liti

def Par.tm: Par α → Tm VPar α := Tm.var ∘ VPar.p
def Var.tm: Var α → Tm VPar α := Tm.var ∘ VPar.v
def VPar.tm: VPar α → Tm VPar α := Tm.var

-- cst1
namespace Tm
  def log     : Tm Γ flt → Tm Γ flt := Tm.cst1 Const1.log
  def exp     : Tm Γ flt → Tm Γ flt := Tm.cst1 Const1.exp
  def sqrt    : Tm Γ flt → Tm Γ flt := Tm.cst1 Const1.sqrt
  def normCdf : Tm Γ flt → Tm Γ flt := Tm.cst1 Const1.normCdf
  def fst     : Tm Γ (α ×× β) → Tm Γ α := Tm.cst1 Const1.fst
  def snd     : Tm Γ (α ×× β) → Tm Γ β := Tm.cst1 Const1.snd
  def sumf    : Tm Γ (array n flt) → Tm Γ flt := Tm.cst1 Const1.sumf
  def suml    : Tm Γ (array n lin) → Tm Γ lin := Tm.cst1 Const1.suml
  def i2n     : Tm Γ (idx n) → Tm Γ nat := Tm.cst1 Const1.i2n
  def n2f     : Tm Γ nat → Tm Γ flt := Tm.cst1 Const1.n2f
  def maxf    : Tm Γ flt → Tm Γ flt → Tm Γ flt := Tm.cst2 Const2.maxf
  def addi  : Tm Γ (idx n) → Tm Γ (idx m) → Tm Γ (idx (n+m)) := Tm.cst2 Const2.addi
  def eqi   : Tm Γ (idx n) → Tm Γ (idx n) → Tm Γ nat := Tm.cst2 Const2.eqi
  -- def fori  : Tm Γ ((idx n ×× α) ~> α) → Tm Γ α → Tm Γ α := Tm.cst2 Const2.fori

  def mkRef: Tm Γ (ref α) := Tm.cst0 Const0.mkRef
  def refGet: Tm Γ (ref α) → Tm Γ α := Tm.cst1 Const1.refGet
  def refSet: Tm Γ (ref α) → Tm Γ α → Tm Γ unit := Tm.cst2 Const2.refSet

  def π: Tm Γ flt := tlitf 3.14159265358979323846

  def linScale: Tm Γ lin → Tm Γ flt → Tm Γ lin := Tm.cst2 (.linScale .mul)
end Tm

def tupleBnd (term: Tm Γ (α××β))(rest: Tm Γ α → Tm Γ β → Tm Γ γ): Tm Γ γ :=
  let' t := term;
  let' f := t.fst;
  let' s := t.snd;
  rest f s

notation:max "let't "f", "s" := "term";"res => tupleBnd term (λ f s => res)

-- cst2
infixl:65 " @@ " => Tm.cst2 Const2.app
notation:max array"[["index"]]" => Tm.cst2 Const2.get array index
def tupple': Tm Γ α → Tm Γ β → Tm Γ (α ×× β) := Tm.cst2 Const2.tup
notation:max "("a",,"b")" => tupple' a b
notation:max "()'" => tlitu

-- refs
def Tm.dumpFor (a: Tm Γ α)(b: Tm Γ β): Tm Γ β := -- otherwise reducible construct to keep ref in tm
  (a,,b) |>.snd
notation:max ref" *:= "term => Tm.refSet ref term
notation:max ref" *:= "term";"k => Tm.dumpFor (Tm.refSet ref term) k
notation:max "let' "xr" :=& "x";"res =>
  let' xr := Tm.mkRef;
  let' x := Tm.refGet xr;
  res
def Tm.useForRef(a: Tm Γ α)
    (refT: (Tm Γ α → Tm Γ β)): Tm Γ α :=
    let' tmp := a;
    refT tmp |>.dumpFor tmp
def Tm.aF (t: Tm Γ α)(f: Tm Γ α → Tm Γ β): Tm Γ β := f t -- apply to function
def Tm.valFromRef (f: Tm Γ α → Tm Γ β): Tm Γ (α.ref) :=
  let' rx :=& x; Tm.dumpFor (f x) rx

@[default_instance] instance [BiArraysC BiLin α β γ]:
  HAdd (Tm Γ α) (Tm Γ β) (Tm Γ γ) := ⟨Tm.cst2 (Const2.linOp add)⟩
@[default_instance] instance [BiArraysC BiLin α β γ]:
  HSub (Tm Γ α) (Tm Γ β) (Tm Γ γ) := ⟨Tm.cst2 (Const2.linOp sub)⟩

@[default_instance] instance [BiArrayC BiLF α β γ]:
  HMul (Tm Γ α) (Tm Γ β) (Tm Γ γ) := ⟨Tm.cst2 (Const2.linScale mul)⟩
@[default_instance] instance [BiArrayC BiLF α β γ]:
  HDiv (Tm Γ α) (Tm Γ β) (Tm Γ γ) := ⟨Tm.cst2 (Const2.linScale div)⟩

@[default_instance] instance [BiArraysC BiArith α β γ]:
  HAdd (Tm Γ α) (Tm Γ β) (Tm Γ γ) := ⟨Tm.cst2 (Const2.arithOp add)⟩
@[default_instance] instance [BiArraysC BiArith α β γ]:
  HSub (Tm Γ α) (Tm Γ β) (Tm Γ γ) := ⟨Tm.cst2 (Const2.arithOp sub)⟩
@[default_instance] instance [BiArraysC BiArith α β γ]:
  HMul (Tm Γ α) (Tm Γ β) (Tm Γ γ) := ⟨Tm.cst2 (Const2.arithOp mul)⟩
@[default_instance] instance [BiArraysC BiArith α β γ]:
  HDiv (Tm Γ α) (Tm Γ β) (Tm Γ γ) := ⟨Tm.cst2 (Const2.arithOp div)⟩

@[default_instance] instance : Max (Tm Γ flt) :=
  ⟨Tm.cst2 Const2.maxf⟩

notation a"<'"b => Tm.cst2 Const2.lt a b
notation a"=='"b => Tm.cst2 Const2.eqi a b

def Tm.inst (α: Ty): Tm Γ α :=
  match α with
  | .nat => Tm.cst0 (Const0.litn 0)
  | .idx _ => Tm.cst0 (Const0.liti 0)
  | .flt => Tm.cst0 (Const0.litf 0)
  | .lin => Tm.cst0 (Const0.litl 0)
  | _ ~> β => Tm.abs (λ _ => Tm.inst β)
  | α ×× β => Tm.cst2 Const2.tup (Tm.inst α) (Tm.inst β)
  | .array _ α => Tm.bld (λ _ => Tm.inst α)
  | .unit => Tm.cst0 Const0.litu
  | .ref _ => panic! "Tm.inst does not support references"

------------------------------------------------------------------------------------------
-- AINF
------------------------------------------------------------------------------------------

-- Prim
notation:max "fun'' "par", "x => Prim.abs par x
notation:max "for'' "par":"n", "x => Prim.bld (par: Par (idx n)) x
notation:max "if'' "cond" then "a" else "b => Prim.ite cond a b
-- bnd
notation:max "let'' "env" in "var" := "prim => (⟨⟨_, var⟩, env, prim⟩: Bnd)
notation:max "let'' "env" in "var":"α" := "prim => (⟨⟨α, var⟩, env, prim⟩: Bnd)

notation:max "let''' "env" in "var" := "prim"; "rest => ((⟨⟨_, var⟩, env, prim⟩: Bnd) :: Prod.fst rest, Prod.snd rest)
notation:max ".ret "v => ([],(v: VPar _))

-- cst0
def plitn: Nat → Prim nat := Prim.cst0 ∘ Const0.litn
def plitf: Float → Prim flt := Prim.cst0 ∘ Const0.litf

namespace Notations

  def x0: Var α := Var.mk 0
  def x1: Var α := Var.mk 1
  def x2: Var α := Var.mk 2
  def x3: Var α := Var.mk 3
  def i0: Par α := Par.mk 0
  def i1: Par α := Par.mk 1
  def i2: Par α := Par.mk 2
  def i3: Par α := Par.mk 3

end Notations
