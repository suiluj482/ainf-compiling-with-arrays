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
-- Env
inductive EnvPart : Type                    --
  | func : (α:Ty) → Par α → EnvPart         -- function control flow
  | forc : (n:Nat) → Par (idx n) → EnvPart  -- for
  | itec : VPar nat → Bool → EnvPart        -- if then else
  deriving DecidableEq
def Env.fromList (e: List EnvPart): Env :=
  e.foldl (λ acc x => match x with
    | .func α p => Env.func acc α p
    | .forc n p => Env.forc acc n p
    | .itec cond ref => Env.itec acc cond ref
    ) Env.nil
def Env.toList: Env → List EnvPart :=
  let rec aux := (λ
  | .nil => []
  | .func acc α p => EnvPart.func α p :: aux acc
  | .forc acc n p => EnvPart.forc n p :: aux acc
  | .itec acc cond ref => EnvPart.itec cond ref :: aux acc)
  List.reverse ∘ aux

-- Prim
notation:max "fun'' "par", "x => Prim.abs par x
notation:max "for'' "par":"n", "x => Prim.bld (par: Par (idx n)) x
notation:max "if'' "cond" then "a" else "b => Prim.ite cond a b
-- bnd
notation:max "let'' "envList" in "var" := "prim"; "ainf => AINF.bnd (Env.fromList envList) var prim ainf

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


-- #eval ((1: Nat):String)
-- open EnvPart Notations
-- #eval [func Ty.nat i0, forc 3 i1] |> Env.fromList |>.toList |> Env.fromList
