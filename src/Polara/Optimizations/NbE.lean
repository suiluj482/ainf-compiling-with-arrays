import Polara.Syntax.Index
import Polara.Codegeneration.Lean.Runtime -- Float.normCdf needed
open Ty Tm Const0 Const1 Const2

------------------------------------------------------------------------------------------
-- normalisation (Polara) by evaluation
------------------------------------------------------------------------------------------

-- denotation - corresponding host-anguage value
@[reducible] def Ty.de (Γ : Ty → Type): Ty → Type
  | nat => Tm Γ nat
  | flt => Tm Γ flt
  | idx i => Tm Γ (idx i)
  | s ×× t => s.de Γ × t.de Γ
  | s ~> t => s.de Γ → t.de Γ
  | array n t => Tm Γ (idx n) → t.de Γ

mutual
  -- denotation to term
  def quote {Γ} : {α : Ty} → Ty.de Γ α → Tm Γ α
    | nat   , e => e
    | flt   , e => e
    | idx _i, e => e
    | _α ~> _β   , e => abs fun x => quote (e (splice (var x)))
    | _α ×× _β   , e => cst2 tup (quote e.1) (quote e.2)
    | array _n _α, e => bld fun x => quote (e (var x))
  -- term to denotation
  def splice {Γ} : {α : Ty} → Tm Γ α → Ty.de Γ α
    | nat   , e => e
    | flt   , e => e
    | idx _i, e => e
    | _α ~> _β   , e => fun x => splice (cst2 app e (quote x))
    | _α ×× _β   , e => (splice (cst1 fst e), splice (cst1 snd e))
    | array _n _α, e => fun x => splice (cst2 get e x)
end

-- #eval quote (splice (Tm.var (α:= Ty.nat ×× Ty.nat) (VPar.v (Var.mk 42)))) |>.pp (0, 0)
-- #reduce quote (splice (Tm.var (α:= Ty.nat ×× Ty.nat) (VPar.v (Var.mk 42))))
-- #reduce splice (Tm.var (α:= Ty.nat ×× Ty.nat) (VPar.v (Var.mk 42)))

def Const0.de : Const0 α → Ty.de Γ α
  | litn n => cst0 (litn n)
  | litf f => cst0 (litf f)
  | liti i => cst0 (liti i)

def Const1.de : Const1 β α → Ty.de Γ β → Ty.de Γ α
  | fst => fun (a , _b) => a
  | snd => fun (_a,  b) => b
  | normCdf => fun
    -- partial evaluation if argument known
    | cst0 (litf a) => cst0 (litf (Float.normCdf a))
    | a             => cst1 normCdf a
  | sqrt => fun
    | cst0 (litf a) => cst0 (litf (Float.sqrt a))
    | a             => cst1 sqrt a
  | exp => fun
    | cst0 (litf a) => cst0 (litf (Float.exp a))
    | a             => cst1 exp a
  | log => fun
    | cst0 (litf a) => cst0 (litf (Float.log a))
    | a             => cst1 log a
  | sum => fun a => splice (cst1 sum (quote a))
  | i2n => fun a => splice (cst1 i2n (quote a))
  | n2f => fun a => splice (cst1 n2f (quote a))

def Tm.isZeroF : Tm Γ α → Bool | cst0 (litf f) => f == 0 | _ => false
def Tm.isOneF  : Tm Γ α → Bool | cst0 (litf f) => f == 1 | _ => false

def Const2.de : Const2 γ β α → Ty.de Γ γ → Ty.de Γ β → Ty.de Γ α
  | app => fun f e => f e
  | get => fun f n => f n
  | tup => fun a b => (a, b)
  | addn => fun
    | err, _ => err
    | _, err => err
    | cst0 (litn a), cst0 (litn b) => cst0 (litn (a + b))
    | a, b                         => cst2 addn a b
  | muln => fun
    | err, _ => err
    | _, err => err
    | cst0 (litn a), cst0 (litn b) => cst0 (litn (a * b))
    | a, b                         => cst2 muln a b
  | addf => fun
    | err, _ => err
    | _, err => err
    | cst0 (litf a), cst0 (litf b) => cst0 (litf (a + b))
    | a, b =>
      if a.isZeroF then b else if b.isZeroF then a else
      cst2 addf a b
  | subf => fun
    | err, _ => err
    | _, err => err
    | cst0 (litf a), cst0 (litf b) => cst0 (litf (a - b))
    | a, b =>
      if b.isZeroF then a else
      cst2 subf a b
  | mulf => fun
    | err, _ => err
    | _, err => err
    | cst0 (litf a), cst0 (litf b) => cst0 (litf (a * b))
    | a, b =>
      if      a.isZeroF || b.isZeroF then cst0 (litf 0)
      else if a.isOneF then b else if b.isOneF then a
      else cst2 mulf a b
  | divf => fun
    | err, _ => err
    | _, err => err
    | cst0 (litf a), cst0 (litf b) => cst0 (litf (a / b))
    | a, b                         => cst2 divf a b
  | maxf => fun
    | err, _ => err
    | _, err => err
    | cst0 (litf a), cst0 (litf b) => cst0 (litf (max a b))
    | a, b                         => cst2 maxf a b
  | addi => cst2 addi

-- term in dessen env sich bereich denotierte terme befinden, im prinzip interpreter
def Tm.de : Tm (Ty.de Γ) α → Ty.de Γ α
  | var i => i
  | err => splice err
  | cst0 k => k.de
  | cst1 k a => k.de a.de
  | cst2 k b a => k.de b.de a.de
  | abs f => fun x => (f x).de
  | bnd e f => (f e.de).de
-- alternatively, if you dont want to reduce binds:
--   | bnd e₁ e₂ =>
--     splice (bnd (quote (reduce e₁)) fun x =>
--       quote (reduce (e₂ (splice (Tm.var x)))))
  | bld f => fun a => (f a).de
  | ite e₁ e₂ e₃ => match e₁.de with
    | cst0 (litn 0) => e₃.de -- 0 is false
    | cst0 (litn _) => e₂.de
    | a'            => splice (ite a' (quote e₂.de) (quote e₃.de))

def Tm.norm {α} : (∀ Γ, Tm Γ α) → Tm Γ α
  | e => quote (de (e _))
