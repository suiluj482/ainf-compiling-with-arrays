import Polara.Syntax.Definitions
import Polara.Syntax.PrettyPrint

open Tm Ty Const0 Const1 Const2

-- Tm
notation:max "let' "x" := "term";"res => Tm.bnd term (λ x => res)
notation:max "fun' "i" => "term => Tm.abs (λ i => term)
notation:max "for' "i" => "term => Tm.bld (λ i => term)
notation:max "for' "i":"n" => "term => Tm.bld (λ (i: VPar (Ty.idx n)) => term)
notation:max "if' "cond" then "a" else "b => Tm.ite cond a b

-- only works with specific type anotations
-- instance : Coe (Γ α) (Tm Γ α) := ⟨(Tm.var ·)⟩
-- instance : Coe (Const0 α) (Tm Γ α) := ⟨(Tm.cst0 ·)⟩
-- instance : Coe (Const1 α β) (Tm Γ α → Tm Γ β) := ⟨(Tm.cst1 · ·)⟩

-- cst0
def tlitn: Nat → Tm Γ nat := Tm.cst0 ∘ Const0.litn
def tlitf: Float → Tm Γ flt := Tm.cst0 ∘ Const0.litf

-- def Nat.tlit: Nat → Term nat := Tm.cst0 ∘ Const0.litn
-- #eval (1).tlit

-- def Float.tlit: Float → Term flt := Tm.cst0 ∘ Const0.litf
-- #eval 1.00.tlit

-- cst1
def log     : Tm Γ flt → Tm Γ flt := Tm.cst1 Const1.log
def exp     : Tm Γ flt → Tm Γ flt := Tm.cst1 Const1.exp
def sqrt    : Tm Γ flt → Tm Γ flt := Tm.cst1 Const1.sqrt
def normCdf : Tm Γ flt → Tm Γ flt := Tm.cst1 Const1.normCdf
def fst     : Tm Γ (α ×× β) → Tm Γ α := Tm.cst1 Const1.fst
def snd     : Tm Γ (α ×× β) → Tm Γ β := Tm.cst1 Const1.snd
def sum     : Tm Γ (array n α) → Tm Γ α := Tm.cst1 Const1.sum
def i2n     : Tm Γ (idx n) → Tm Γ nat := Tm.cst1 Const1.i2n
def n2f     : Tm Γ nat → Tm Γ flt := Tm.cst1 Const1.n2f

-- cst2
infixl:65 " @@ " => Tm.cst2 Const2.app
notation:max array"[["index"]]" => Tm.cst2 Const2.get array index

def tupple': Tm Γ α → Tm Γ β → Tm Γ (α ×× β) := Tm.cst2 Const2.tup

instance : Add (Tm Γ flt) := ⟨Tm.cst2 Const2.addf⟩
instance : Sub (Tm Γ flt) := ⟨Tm.cst2 Const2.subf⟩
instance : Mul (Tm Γ flt) := ⟨Tm.cst2 Const2.mulf⟩
instance : Div (Tm Γ flt) := ⟨Tm.cst2 Const2.divf⟩
instance : Max (Tm Γ flt) := ⟨Tm.cst2 Const2.maxf⟩
instance : Add (Tm Γ nat) := ⟨Tm.cst2 Const2.addn⟩
instance : Mul (Tm Γ nat) := ⟨Tm.cst2 Const2.muln⟩

-- #eval (for' i:2 => i2n (var i) : Term (array 2 nat)) |>.pretty

------------------------------------------------------------------------------------------
-- AINF
------------------------------------------------------------------------------------------
notation:max "func'' "par":"α", "rest => Env.func rest α par
notation:max "forc'' "par":"n", "rest => Env.forc rest n par
notation:max "itec'' "cond":"ref", "rest => Env.ite rest cond ref
notation:max "let'' "env" of "var" := "prim"; "ainf => AINF.bnd env var prim ainf

-- def i0: Par Ty.nat := Par.mk 0
-- #eval (func'' i0:Ty.nat, Env.nil) |>.pretty
-- def x0: Var Ty.nat := Var.mk 0
-- #eval let'' Env.nil of x0 := (Prim.cst0 (litn 0)); AINF.ret (VPar.v x0)
-- #eval let'' (func'' i0:Ty.nat, Env.nil) of x0 := (Prim.cst0 (litn 0)); AINF.ret (VPar.v x0)
