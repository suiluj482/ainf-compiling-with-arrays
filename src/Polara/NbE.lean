import Polara.Syntax
open Ty Tm Const0 Const1 Const2

------------------------------------------------------------------------------------------
-- normalisation (Polara)
------------------------------------------------------------------------------------------

@[reducible] def Ty.de (Γ : Ty → Type): Ty → Type
  | nat => Tm Γ nat
  | flt => Tm Γ flt
  | idx i => Tm Γ (idx i)
  | s ×× t => s.de Γ × t.de Γ
  | s ~> t => s.de Γ → t.de Γ
  | array n t => Tm Γ (idx n) → t.de Γ

mutual
  def quote {Γ} : {α : Ty} → Ty.de Γ α → Tm Γ α
    | α ~> β, e => abs fun x => quote (e (splice (var x)))
    | α ×× β, e => cst2 tup (quote e.1) (quote e.2)
    | nat, e => e
    | flt, e => e
    | idx _i, e => e
    | array n α, e => bld fun x => quote (e (var x))
  def splice {Γ} : {α : Ty} → Tm Γ α → Ty.de Γ α
    | α ~> β, e => fun x => splice (cst2 app e (quote x))
    | α ×× β, e => (splice (cst1 fst e), splice (cst1 snd e))
    | nat, e => e
    | flt, e => e
    | idx _i, e => e
    | array n α, e => fun x => splice (cst2 get e x)
end

-- https://github.com/tpn/cuda-samples/blob/master/v9.0/4_Finance/BlackScholes/BlackScholes_gold.cpp
def Float.normCdf (d: Float): Float :=
  let       A1 :=  0.31938153
  let       A2 := -0.356563782
  let       A3 :=  1.781477937
  let       A4 := -1.821255978
  let       A5 :=  1.330274429
  let RSQRT2PI :=  0.39894228040143267793994605993438
  let K := 1.0 / (1.0 + 0.2316419 * d.abs)
  let cnd := RSQRT2PI * Float.exp (- 0.5 * d * d) *
    (K * (A1 + K * (A2 + K * (A3 + K * (A4 + K * A5)))))
  if d > 0 then 1.0 - cnd else cnd

def Const0.de : Const0 α → Ty.de Γ α
  | litn n => cst0 (litn n)
  | litf f => cst0 (litf f)
  | liti i => cst0 (liti i)

def Const1.de : Const1 β α → Ty.de Γ β → Ty.de Γ α
  | fst => fun (a, _b) => a
  | snd => fun (_a, b) => b
  | normCdf => fun
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

def Tm.isZero : Tm Γ α → Bool | cst0 (litf f) => f == 0 | _ => false
def Tm.isOne  : Tm Γ α → Bool | cst0 (litf f) => f == 1 | _ => false

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
      if a.isZero then b else if b.isZero then a else
      cst2 addf a b
  | subf => fun
    | err, _ => err
    | _, err => err
    | cst0 (litf a), cst0 (litf b) => cst0 (litf (a - b))
    | a, b =>
      if b.isZero then a else
      cst2 subf a b
  | mulf => fun
    | err, _ => err
    | _, err => err
    | cst0 (litf a), cst0 (litf b) => cst0 (litf (a * b))
    | a, b =>
      if      a.isZero || b.isZero then cst0 (litf 0)
      else if a.isOne then b else if b.isOne then a
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
