import Polara.Syntax.All
import Polara.Codegeneration.Lean.Runtime -- Float.normCdf needed
open Ty Tm Const0 Const1 ArithOp AddOp MulOp Const2

------------------------------------------------------------------------------------------
-- normalisation (Polara) by evaluation
------------------------------------------------------------------------------------------

-- denotation - corresponding host-anguage value
@[reducible] private def Ty.de (Γ : Ty → Type): Ty → Type
| nat => Tm Γ nat
| flt => Tm Γ flt
| lin => Tm Γ lin
| idx i => Tm Γ (idx i)
| s ×× t => s.de Γ × t.de Γ
| s ~> t => s.de Γ → t.de Γ
| array n t => Tm Γ (idx n) → t.de Γ
| unit => Tm Γ unit
| list α => Tm Γ (list α)

instance: Inhabited (Ty.de Γ α) :=
  ⟨
    let rec go := λ
    | .nat => tlitn 0
    | .flt => tlitf 0
    | .lin => tlitlZ
    | .idx _ => tliti 0
    | α ×× β => (go α, go β)
    | _ ~> β => λ _ => go β
    | .array _ α => λ _ => go α
    | .unit => tlitu
    | list _ => tlitlE
    go α
  ⟩

-- schwache starke c(...) Eta gesetz
mutual
  -- denotation to term
  private def quote {Γ} : {α : Ty} → α.de Γ → Tm Γ α
  | unit  , e => e
  | nat   , e => e
  | flt   , e => e
  | lin   , e => e
  | idx _i, e => e
  | _α ~> _β   , e => fun' x => quote (e (splice x))
  | _α ×× _β   , e => (quote e.1,, quote e.2)
  | array _n _α, e => for' x => quote (e x)
  | list _, e => e
  -- term to denotation
  private def splice {Γ} : {α : Ty} → Tm Γ α → Ty.de Γ α
  | unit  , e => e
  | nat   , e => e
  | flt   , e => e
  | lin   , e => e
  | idx _i, e => e
  | _α ~> _β   , e => λ x => splice (e @@ (quote x))
  | _α ×× _β   , e => (splice e.fst, splice e.snd)
  | array _n _α, e => fun x => splice (e[[x]])
  | list _, e => e
end

private def Const0.de : Const0 α → Ty.de Γ α
| litn n => tlitn n
| litf f => tlitf f
| litlZ => tlitlZ
| liti i => tliti i
| litu => tlitu
| litlE => tlitlE

private def Const1.de : Const1 β α → Ty.de Γ β → Ty.de Γ α
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
| sumf => fun a => splice (cst1 sumf (quote a))
| suml => fun a => splice (cst1 suml (quote a))
| i2n => fun
  | cst0 (liti a) => tlitn a
  | a => splice (cst1 i2n (quote a))
| n2f => fun
  | cst0 (litn a) => tlitf a.toFloat
  | a => splice (cst1 n2f (quote a))
| arr2list => λ a => splice (quote a).arr2list

private def Tm.isZeroF : Tm Γ α → Bool | cst0 (litf f) => f == 0 | _ => false
private def Tm.isOneF  : Tm Γ α → Bool | cst0 (litf f) => f == 1 | _ => false

private def arithOpDe (op: ArithOp): BiArrays BiArith α' β' γ'
→ Ty.de Γ α' → Ty.de Γ β' → Ty.de Γ γ'
| .array n type =>
  (λ a b i => arithOpDe op type (a i) (b i))
| .base t => match t with
  | .nats =>
    match op with
    | .add => fun
      | .err, _ | _, .err => err
      | cst0 (litn a), cst0 (litn b) => cst0 (litn (a + b))
      | cst0 (litn 0), c
      | c, cst0 (litn 0) => c
      | a, b => cst2 (arithOp add) a b
    | .sub => fun
      | .err, _ | _, .err => err
      | cst0 (litn a), cst0 (litn b) => cst0 (litn (a - b))
      | c, cst0 (litn 0) => c
      | a, b => cst2 (arithOp sub) a b
    | .mul => fun
      | .err, _ | _, .err => err
      | cst0 (litn a), cst0 (litn b) => cst0 (litn (a * b))
      | a, b => cst2 (arithOp mul) a b
    | .div => fun
      | .err, _ | _, .err => err
      | cst0 (litn a), cst0 (litn b) => if b == 0 then err else cst0 (litn (a / b))
      | a, b => cst2 (arithOp div) a b
  | .flts =>
    match op with
    | .add => fun
      | .err, _ | _, .err => err
      | cst0 (litf a), cst0 (litf b) => cst0 (litf (a + b))
      | a, b =>
        if a.isZeroF then b else if b.isZeroF then a else
        cst2 (arithOp add) a b
    | .sub => fun
      | .err, _ | _, .err => err
      | cst0 (litf a), cst0 (litf b) => cst0 (litf (a - b))
      | a, b =>
        if b.isZeroF then a else
        cst2 (arithOp sub) a b
    | .mul => fun
      | .err, _ | _, .err => err
      | cst0 (litf a), cst0 (litf b) => cst0 (litf (a * b))
      | a, b =>
        if      a.isZeroF || b.isZeroF then cst0 (litf 0)
        else if a.isOneF then b else if b.isOneF then a
        else cst2 (arithOp mul) a b
    | .div => fun
      | .err, _ | _, .err => err
      | cst0 (litf a), cst0 (litf b) =>
        if b == 0 then err else cst0 (litf (a / b))
      | a, b => cst2 (arithOp div) a b
private def linOpDe (op: AddOp): BiArrays BiLin α' β' γ' → Ty.de Γ α' → Ty.de Γ β' → Ty.de Γ γ'
| .array n type =>
  (λ a b i => linOpDe op type (a i) (b i))
| .base t => match t with
  | .lins =>
    match op with
    | .add => fun
      | .err, _ | _, .err => err
      | cst0 litlZ, a | a, cst0 litlZ => a
      | a, b => a + b
    | .sub => fun
      | .err, _ | _, .err => err
      | a, cst0 litlZ => a
      | a, b => a - b
private def linScaleDe (op: MulOp) : BiLF α' β' γ' → Ty.de Γ α' → Ty.de Γ β' → Ty.de Γ γ'
| .lf => match op with
  | .mul => fun
    | .err, _ | _, .err => err
    | cst0 litlZ, _ => tlitlZ
    | a, b =>
      if b.isZeroF then tlitlZ
      else if b.isOneF then a
      else a * b
  | .div => fun
    | .err, _ | _, .err => err
    | cst0 litlZ, _ => tlitlZ
    | a, b =>
      if b.isZeroF then err
      else if b.isOneF then a
      else a / b

private def Const2.de : Const2 α β γ → Ty.de Γ α → Ty.de Γ β → Ty.de Γ γ
| app => fun f e => f e
| get => fun f n => f n
| tup => λ
  | a, b => (a, b)
| lt => fun
  | .err, _
  | _, .err => err
  | cst0 (litf a), cst0 (litf b) => cst0 (litn (if a<b then 1 else 0))
  | a, b                         => cst2 lt a b
| maxf => fun
  | .err, _ => err
  | _, .err => err
  | cst0 (litf a), cst0 (litf b) => cst0 (litf (max a b))
  | a, b                         => cst2 maxf a b
| addi => fun
  | .err, _
  | _, err => err
  | cst0 (liti a (n:=n)), cst0 (liti b (n:=m)) =>
      tliti (Pos.addMinOne_eq_add_min_one▸a.add' b)
  | a, b => cst2 addi a b
| eqi => fun
  | .err, _
  | _, err => err
  | cst0 (liti a), cst0 (liti b) => if a==b then tlitn 1 else tlitn 0
  | a, b => cst2 eqi a b
| @arithOp _ _ _ type op => arithOpDe op type.t
| @linOp _ _ _ type op =>
  linOpDe op type.t
| @linScale _ _ _ type op =>
  match type.t with
  | .array n t =>
    (λ a b i => linScaleDe op t (a i) (b i))
  | .base t => linScaleDe op t
| @cons _ => λ
  | e, l => (quote e).cons l
| @append _ => λ
  | .err, _ | _, .err => err
  | cst0 litlE, a | a, cst0 litlE => a
  | cst2 .cons a (cst0 litlE), l => a.cons l
  | cst2 .cons a (cst2 .cons b (cst0 litlE)), l => a.cons (b.cons l)
  | a, b => a.append b
| @zipL _ _ => λ
  | .err, _ | _, .err => err
  | cst0 litlE, _ | _, cst0 litlE => tlitlE
  | a, b => a.zipL b
| @mapL _ _ => λ
  | .err, _ => err
  | cst0 litlE, _ => tlitlE
  | a, b => a.mapL (quote b)
| @foldL _ _ => λ
  | .err, _ => splice .err
  | cst0 litlE, (_,n) => n
  | cst2 cons e (cst0 litlE), (f,n) => f (splice e) n
  | l, (f, n) => splice (l.foldL (quote f) (quote n))
| @foldA _ _ _ => λ
  | arr, (f, n) => splice ((quote arr).foldA (quote f) (quote n))

-- term in dessen env sich bereich denotierte terme befinden, im prinzip interpreter
private def Tm.de : Tm (Ty.de Γ) α → Ty.de Γ α
  | var i => i
  | err => splice err
  | cst0 k => k.de
  | cst1 k a => k.de a.de
  | cst2 k b a => k.de b.de a.de
  | abs f => fun x => (f x).de
  | bnd e f => (f e.de).de
  | bld f => fun a => (f a).de
  | ite e₁ e₂ e₃ => match e₁.de with
    | cst0 (litn 0) => e₃.de -- 0 is false
    | cst0 (litn _) => e₂.de
    | a'            => splice (ite a' (quote e₂.de) (quote e₃.de))

-- private def Tm.safeDe : Tm (Ty.de Γ) α → Ty.de Γ α
--   | var i => i
--   | err => splice err
--   | cst0 k => k.de
--   | cst1 k a => k.de a.de
--   | cst2 k b a => k.de b.de a.de
--   | abs f => fun x => (f x).de
--   | bnd e₁ e₂ =>
--     splice (bnd (quote (reduce e₁)) fun x =>
--       quote (reduce (e₂ (splice (Tm.var x)))))
--   | bld f => fun a => (f a).de
--   | ite e₁ e₂ e₃ => match e₁.de with
--     | cst0 (litn 0) => e₃.de -- 0 is false
--     | cst0 (litn _) => e₂.de
--     | a'            => splice (ite a' (quote e₂.de) (quote e₃.de))

def Tm.norm {α} : (∀ Γ, Tm Γ α) → Tm Γ α
  | e => quote (de (e _))

def Tm.normVPar (t: Tm VPar α): Tm VPar α :=
  Tm.norm (λ _ => t.generalizeVPar)

-- #eval ((norm (fun Γ => ((fun' i0 => i0): Tm Γ (Ty.nat ~> Ty.nat)))) : Tm VPar (Ty.nat ~> Ty.nat))
-- #eval (fun x => x) 0

-- #eval (
--   let' f := (fun' x:flt => x+x);
--   let' fd := (f,, f);
--   fun' x:flt => (fd.fst @@ x) + (fd.snd @@ x)
-- ).normVPar

-- #eval (
--   let' f := (fun' x:flt => x+x);
--   let' g := (fun' x:flt => x+x);
--   fun' a:nat => (fun' x:flt => ((if' a then f else g) @@ x))
-- ).normVPar
