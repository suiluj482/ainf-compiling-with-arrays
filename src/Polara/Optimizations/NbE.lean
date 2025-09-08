import Polara.Syntax.Index
import Polara.Codegeneration.Lean.Runtime -- Float.normCdf needed
open Ty Tm Const0 Const1 ArithOp AddOp MulOp Const2

------------------------------------------------------------------------------------------
-- normalisation (Polara) by evaluation
------------------------------------------------------------------------------------------

-- denotation - corresponding host-anguage value
@[reducible] def Ty.de (Γ : Ty → Type): Ty → Type
  | nat => Tm Γ nat
  | flt => Tm Γ flt
  | lin => Tm Γ lin
  | idx i => Tm Γ (idx i)
  | s ×× t => s.de Γ × t.de Γ
  | s ~> t => s.de Γ → t.de Γ
  | array n t => Tm Γ (idx n) → t.de Γ
  | unit => Tm Γ unit
  | ref _ => Unit -- not supported in term

instance: Inhabited (Ty.de Γ α) :=
  ⟨
    let rec go := λ
    | .nat => cst0 (litn 0)
    | .flt => cst0 (litf 0)
    | .lin => cst0 (litl 0)
    | .idx _ => cst0 (liti 0)
    | α ×× β => (go α, go β)
    | _ ~> β => λ _ => go β
    | .array _ α => λ _ => go α
    | .unit => cst0 litu
    | .ref _ => ()
    go α
  ⟩

-- schwache starke c(...) Eta gesetz
mutual
  -- denotation to term
  def quote {Γ} : {α : Ty} → Ty.de Γ α → Tm Γ α
    | unit  , e => e
    | nat   , e => e
    | flt   , e => e
    | lin   , e => e
    | idx _i, e => e
    | _α ~> _β   , e => abs fun x => quote (e (splice (var x)))
    | _α ×× _β   , e => cst2 tup (quote e.1) (quote e.2)
    | array _n _α, e => bld fun x => quote (e (var x))
    | .ref _α, _ => panic! "ref not supported in denotation"
  -- term to denotation
  def splice {Γ} : {α : Ty} → Tm Γ α → Ty.de Γ α
    | unit  , e => e
    | nat   , e => e
    | flt   , e => e
    | lin   , e => e
    | idx _i, e => e
    | _α ~> _β   , e => fun x => splice (cst2 app e (quote x))
    | _α ×× _β   , e => (splice (cst1 fst e), splice (cst1 snd e))
    | array _n _α, e => fun x => splice (cst2 get e x)
    | .ref _α, _ => panic! "ref not supported in denotation"
end

def Const0.de : Const0 α → Ty.de Γ α
  | litn n => cst0 (litn n)
  | litf f => cst0 (litf f)
  | litl l => cst0 (litl l)
  | liti i => cst0 (liti i)
  | litu => cst0 litu
  | mkRef => panic! "ref not supported in denotation"

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
  | sumf => fun a => splice (cst1 sumf (quote a))
  | suml => fun a => splice (cst1 suml (quote a))
  | i2n => fun a => splice (cst1 i2n (quote a))
  | n2f => fun a => splice (cst1 n2f (quote a))
  | refGet => panic! "ref not supported in denotation"

def Tm.isZeroF : Tm Γ α → Bool | cst0 (litf f) => f == 0 | _ => false
def Tm.isOneF  : Tm Γ α → Bool | cst0 (litf f) => f == 1 | _ => false

def Tm.isZeroL : Tm Γ α → Bool | cst0 (litl f) => f == 0 | _ => false
def Tm.isOneL : Tm Γ α → Bool | cst0 (litl f) => f == 1 | _ => false

def Const2.de : Const2 α β γ → Ty.de Γ α → Ty.de Γ β → Ty.de Γ γ
  | app => fun f e => f e
  | get => fun f n => f n
  | tup => fun a b => (a, b)
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
    -- | cst0 (liti a), cst0 (liti b) => tliti (a.add' b)
    | a, b => cst2 addi a b
  | eqi => fun
    | .err, _
    | _, err => err
    | cst0 (liti a), cst0 (liti b) => if a==b then tlitn 1 else tlitn 0
    | a, b => cst2 eqi a b
  | @arithOp _ _ _ type op =>
    let rec goA {α' β' γ': Ty}: BiArrays BiArith α' β' γ' → Ty.de Γ α' → Ty.de Γ β' → Ty.de Γ γ' :=
      (λ
        | .array n type =>
          (λ a b i => goA type (a i) (b i))
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
      )
    goA type.t
  | @linOp _ _ _ type op =>
    let rec goL {α' β' γ': Ty}: BiArrays BiLin α' β' γ' → Ty.de Γ α' → Ty.de Γ β' → Ty.de Γ γ' :=
      (λ
        | .array n type =>
          (λ a b i => goL type (a i) (b i))
        | .base t => match t with
          | .lins =>
            match op with
            | .add => fun
              | .err, _ | _, .err => err
              | cst0 (litl a), cst0 (litl b) => cst0 (litl (a + b))
              | a, b =>
                if a.isZeroL then b else if b.isZeroL then a else
                cst2 (linOp add) a b
            | .sub => fun
              | .err, _ | _, .err => err
              | cst0 (litl a), cst0 (litl b) => cst0 (litl (a - b))
              | a, b =>
                if b.isZeroL then a else
                cst2 (linOp sub) a b
      )
    goL type.t
  | @linScale _ _ _ type op =>
    let rec goS {α' β' γ': Ty}: BiLF α' β' γ' → Ty.de Γ α' → Ty.de Γ β' → Ty.de Γ γ' :=
      (λ
        | .lf => match op with
          | .mul => fun
            | .err, _ | _, .err => err
            | cst0 (litl a), cst0 (litf b) => cst0 (litl (a * b))
            | a, b =>
              if      a.isZeroL || b.isZeroL then cst0 (litl 0)
              else if b.isOneL then a
              else cst2 (linScale mul) a b
          | .div => fun
            | .err, _ | _, .err => err
            | cst0 (litl a), cst0 (litf b) =>
              if b == 0 then err else cst0 (litl (a / b))
            | a, b => cst2 (linScale div) a b
      )
    match type.t with
    | .array n t =>
      (λ a b i => goS t (a i) (b i))
    | .base t => goS t
  | refSet => panic! "ref not supported in denotation"

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

def Tm.normVPar (t: Tm VPar α): Tm VPar α :=
  Tm.norm (λ _ => t.generalizeVPar)

-- #eval ((norm (fun Γ => ((fun' i0 => i0): Tm Γ (Ty.nat ~> Ty.nat)))) : Tm VPar (Ty.nat ~> Ty.nat))
-- #eval (fun x => x) 0

#eval (
  let' f := (fun' x:flt => x+x);
  let' fd := (f,, f);
  fun' x:flt => (fd.fst @@ x) + (fd.snd @@ x)
).normVPar

#eval (
  let' f := (fun' x:flt => x+x);
  let' g := (fun' x:flt => x+x);
  fun' a:nat => (fun' x:flt => ((if' a then f else g) @@ x))
).normVPar
