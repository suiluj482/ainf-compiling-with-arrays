import Polara.Syntax.All
open Std

-- https://github.com/tpn/cuda-samples/blob/master/v9.0/4_Finance/BlackScholes/BlackScholes_gold.cpp
private def Float.normCdf (d: Float): Float :=
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

-- kein clock überlauf
private def Fin.add' : Fin n → Fin m → Fin (n-1+m)
| ⟨x, hx⟩, ⟨y, hy⟩ => ⟨x+y,
  let ⟨ x', hx' ⟩ := Nat.le.dest hx;
  let ⟨ y', hy' ⟩ := Nat.le.dest hy;
  Nat.le.intro (k := x' + y') (by simp! +arith [←hx', ←hy']) ⟩

structure Cost where
  consts: Nat
  typeConversions: Nat
  ops: Nat
  tuples: Nat
  controlFlows: Nat
  varDefs: Nat
  varUses: Nat
abbrev CostM := λ α => (StateM Cost (Option α))
def Cost.zero: Cost := ⟨0,0,0,0,0,0,0⟩
def Cost.const: Cost → Cost | c => {c with consts := c.consts + 1}
def Cost.typeConversion: Cost → Cost | c => {c with typeConversions := c.typeConversions + 1}
def Cost.op: Cost → Cost | c => {c with ops := c.ops + 1}
def Cost.vectorOp: Cost → Nat → Cost | c, n => {c with ops := c.ops + n}
def Cost.tuple: Cost → Cost | c => {c with tuples := c.tuples + 1}
def Cost.controlFlow: Cost → Cost | c => {c with controlFlows := c.controlFlows + 1}
def Cost.varDef: Cost → Cost | c => {c with varDefs := c.varDefs + 1}
def Cost.varUse: Cost → Cost | c => {c with varUses := c.varUses + 1}
def Cost.add (a b: Cost): Cost :=
  { consts := a.consts + b.consts,
    typeConversions := a.typeConversions + b.typeConversions,
    ops := a.ops + b.ops,
    tuples := a.tuples + b.tuples,
    controlFlows := a.controlFlows + b.controlFlows,
    varDefs := a.varDefs + b.varDefs,
    varUses := a.varUses + b.varUses }

@[reducible]
def Ty.val': Ty → Type
| .nat => Nat
| .flt => Float
| .lin => Float
| .unit => Unit
| .idx n => Fin n
| α ×× β => α.val' × β.val'
| .array n α => Vector α.val' n
| α ~> β => α.val' → CostM β.val'
| .list α => List α.val'

def Ty.val: Ty → Type | α => CostM α.val'

instance: Inhabited (Ty.val' α) :=
  ⟨
    let rec go := λ
    | .nat => 0
    | .flt => 0.0
    | .lin => 0.0
    | .idx _ => 0
    | α ×× β => (go α, go β)
    | _ ~> β => λ _ => λ _ => (go β, .zero)
    | .array n α => Vector.replicate n (go α)
    | .unit => ()
    | .list _ => []
    go α
  ⟩
instance: Inhabited (Ty.val α) := ⟨λ _ => (Inhabited.default, .zero)⟩

def Regs := DHashMap (Sigma VPar) (λ ⟨α,_⟩ => α.val)

def Const0.val: Const0 α → α.val
| .litn n => λ c => (n, c.const)
| .litf f => λ c => (f, c.const)
| .litlZ => λ c => (some 0, c.const)
| .liti i => λ c => (i, c.const)
| .litu => λ c => ((), c.const)
| .litlE => λ c => (some [], c.const)

def Const1.val (a: α.val'): Const1 α β → β.val
| .i2n => λ c => (a.val, c.typeConversion)
| .n2f => λ c => (Float.ofNat a, c.typeConversion)
| .fst => λ c => (a.fst, c.tuple)
| .snd => λ c => (a.snd, c.tuple)
| .sqrt => λ c => (Float.sqrt a, c.op)
| .log => λ c => (Float.log a, c.op)
| .exp => λ c => (Float.exp a, c.op)
| .normCdf => λ c => (Float.normCdf a, c.op)
| .sumf (n:=n) => λ c => (some (a.foldl (· + ·) 0.0), c.vectorOp n)
| .suml (n:=n) => λ c => (some (a.foldl (· + ·) 0.0), c.vectorOp n)
| .arr2list => λ c => (a.toArray.toList, c.typeConversion)

def ArithOp.val (op: ArithOp): BiArrays BiArith α β γ →
α.val' → β.val' → γ.val
| .array n t (γ:=γ') => λ a b =>
    let v := Vector.zipWith (op.val t · ·) a b
    v.mapM (λ (x: CostM γ'.val') => x)
| .base t => match t with
  | .nats => match op with
    | .add => λ a b c => (a + b, c.op)
    | .sub => λ a b c => (a - b, c.op)
    | .mul => λ a b c => (a * b, c.op)
    | .div => λ a b c => (a / b, c.op)
  | .flts => match op with
    | .add => λ a b c => (a + b, c.op)
    | .sub => λ a b c => (a - b, c.op)
    | .mul => λ a b c => (a * b, c.op)
    | .div => λ a b c => (a / b, c.op)

def Const2.val (a: α.val')(b: β.val'): Const2 α β γ → γ.val
| @arithOp _ _ _ t op => ArithOp.val op t.t a b
| linOp _ => panic! "linOp not implemented"
| linScale _ => panic! "linScale not implemented"
| .lt => λ c => (if a < b then 1 else 0, c.op)
| .maxf => λ c => (if a < b then b else a, c.op)
| .addi => λ c => (a.add' b, c.op)
| .eqi => λ c => (if a == b then 1 else 0, c.op)
| .tup => λ c => ((a, b), c.tuple)
| .app => a b
| .get => λ c => (a.get b, c.op)
| .cons => λ c => (a :: b, c.op)
| .append => λ c => (a ++ b, c.op)
| .zipL => λ c => (List.zip a b, c.op)
| .mapL => a.mapM b
| .foldL (β:=β') => panic! "foldL not implemented"
| .foldA (β:=β') => panic! "foldA not implemented"

def Tm.val: Tm VPar α → α.val
| .err => panic! "Tm.err evaluated"
