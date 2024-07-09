import Polara.CSE
import Polara.NbE
import Polara.Codegen

open Tm Ty Const0 Const1 Const2

def AINF.toString : AINF α → String | e => e.pretty id
instance : ToString (AINF α) where toString x := x.toString

instance : Add (Tm Γ flt) where add e f := cst2 .addf e f
instance : Sub (Tm Γ flt) where sub e f := cst2 .subf e f
instance : Mul (Tm Γ flt) where mul e f := cst2 .mulf e f
instance : Div (Tm Γ flt) where div e f := cst2 .divf e f

def log  : Tm Γ flt → Tm Γ flt := fun x => cst1 .log x
def exp  : Tm Γ flt → Tm Γ flt := fun x => cst1 .exp x
def sqrt : Tm Γ flt → Tm Γ flt := fun x => cst1 .sqrt x
def normCdf : Tm Γ flt → Tm Γ flt := fun x => cst1 .normCdf x

------------------------------------------------------------------------------------------
-- Black scholes
------------------------------------------------------------------------------------------

def calls: Tm Γ (flt ~> flt ~> flt ~> flt ~> flt ~> flt) :=
  abs fun S => abs fun K => abs fun T => abs fun r => abs fun sigma =>
  bnd ((log (var S / var K) + (var r + var sigma * var sigma / cst0 (litf 2)) * var T) / (var sigma * sqrt (var T))) fun d1 =>
  bnd (var d1 - var sigma * sqrt (var T)) fun d2 =>
  var S * normCdf (var d1) - var K * (exp (cst0 (litf 0) - var r * var T)) * normCdf (var d2)

def puts: Tm Γ (flt ~> flt ~> flt ~> flt ~> flt ~> flt) :=
  abs fun S => abs fun K => abs fun T => abs fun r => abs fun sigma =>
  bnd ((log (var S / var K) + (var r + var sigma * var sigma / cst0 (litf 2)) * var T) / (var sigma * sqrt (var T))) fun d1 =>
  bnd (var d1 - var sigma * sqrt (var T)) fun d2 =>
  var K * exp (cst0 (litf 0) - var r * var T) * normCdf (cst0 (litf 0) - var d2) - var S * normCdf (cst0 (litf 0) - var d1)

def mainBlackScholes : Tm Γ (array n flt ~> array n (flt ×× flt)) :=
  abs fun arr =>
  bnd (cst0 (litf 1)) fun S =>
  bnd (cst0 (litf 1)) fun K =>
  bnd (cst0 (litf 1)) fun r =>
  bnd (cst0 (litf 1)) fun sigma =>
  bnd (bld fun i =>
    calls @@ var S @@ var K @@ (cst2 get (var arr) (var i)) @@ var r @@ var sigma)
  fun Calls: Γ (array n flt) =>
  bnd (bld fun i =>
    puts @@ var S @@ var K @@ (cst2 get (var arr) (var i)) @@ var r @@ var sigma)
  fun Puts: Γ (array n flt) =>
  bld fun i => cst2 tup (cst2 get (var Calls) (var i)) (cst2 get (var Puts) (var i))

-- #eval (Tm.norm (mainBlackScholes (Γ:=.) (n:=1))).toAINF
-- #eval (Tm.norm (mainBlackScholes (Γ:=.) (n:=10))).toAINF.cse [] []

------------------------------------------------------------------------------------------
-- dense example
------------------------------------------------------------------------------------------

-- dense(b: [n]Float, W: [n,m]Float, x: [m]Float) :=
  -- for i. max(0, (sum j. W[i,j] * x[j]) + b[i])

def dense {Γ : Ty → Type} n m : Tm Γ (
  array n flt ~> array n (array m flt) ~> array m flt ~> array n flt
) :=
  abs fun b => abs fun W => abs fun x =>
  bld fun i => cst2 maxf (cst0 (litf 0)) (cst2 addf
    (cst1 sum (bld fun j =>
      cst2 mulf (cst2 get (cst2 get (var W) (var i)) (var j)) (cst2 get (var x) (var j))))
    (cst2 get (var b) (var i)))

------------------------------------------------------------------------------------------
-- conv example
------------------------------------------------------------------------------------------

-- conv(x: [n]Float, y: [m]Float) : [n+m−1]Float :=
  -- for i. sum j. x[j] * y[i+j]

def conv {Γ : Ty → Type} n m : Tm Γ (
  array n flt ~> array (n+m-1) flt ~> array m flt
) :=
  abs fun x => abs fun y =>
  bld fun i =>
  cst1 sum (bld fun j =>
  cst2 mulf (cst2 get (var x) (var j)) (cst2 get (var y) (cst2 addi (var j) (var i)))
  )

------------------------------------------------------------------------------------------
-- CSE test for loop
------------------------------------------------------------------------------------------

def loop1 {Γ : Ty → Type} n : Tm Γ ((array n nat) ×× (array n nat)) :=
  bnd (bld fun _i =>
    bnd (cst0 (litn n)) fun t =>
    cst2 addn (var t) (cst0 (litn 1))
  ) fun l0 =>
  bnd (bld fun _i =>
    bnd (cst0 (litn n)) fun t =>
    cst2 muln (var t) (cst0 (litn 2))
  ) fun l1 =>
  (cst2 tup (var l0) (var l1))

def incr (t : Tm Γ nat) : Tm Γ nat :=
  cst2 addn t (cst0 (litn 1))

--x = for i.
-- ys = f(xs[i])
-- zs = f(xs[i])
-- (ys,zs)
--(for i: fst x[i])
def foo : Tm Γ (array n nat ~> array n nat) :=
  abs λ xs =>
    bnd
      (bld λ i =>
        cst2 tup
          (incr (cst2 get (var xs) (var i)))
          (incr (cst2 get (var xs) (var i))))
      λ x : Γ (array n (product nat nat)) =>
        bld λ i => (cst1 fst (cst2 get (var x) (var i)))

------------------------------------------------------------------------------------------
-- CSE test for if-then-else
------------------------------------------------------------------------------------------

-- partial redundancy test
def cseTest1 {Γ : Ty → Type} : Tm Γ (Ty.nat ~> Ty.nat) :=
  abs fun x => -- 1+x should be shared across the branches
    ite (var x)
      (cst2 addn (cst0 (litn 42)) (cst2 addn (cst0 (litn 1)) (var x)))
      (cst2 addn (cst0 (litn 24)) (cst2 addn (cst0 (litn 1)) (var x)))

def cseTest2 {Γ : Ty → Type} : Tm Γ (Ty.nat ~> Ty.nat) :=
  abs fun x => -- 1+x should be shared across the beginning and the branch
    bnd (cst2 addn (cst0 (litn 1)) (var x)) fun _l0 =>
    ite (var x)
      (var x)
      (cst2 addn (cst0 (litn 1)) (var x))

def cseTest3 {Γ : Ty → Type} : Tm Γ (Ty.nat ~> Ty.nat) :=
  abs fun x => -- 1+x should be shared across the branch and the end
    bnd (ite
      (var x)
      (var x)
      (cst2 addn (cst0 (litn 1)) (var x))
    ) fun _l0 =>
    (cst2 addn (cst0 (litn 1)) (var x))

#eval cseTest1.toAINF.cse [] []

------------------------------------------------------------------------------------------
-- PE & CSE test
------------------------------------------------------------------------------------------

def egyptLean (n: Nat) (x: Nat) :=
  n ^ (2 ^ x)

def egypt (n: Nat) {Γ : Ty → Type} : Tm Γ (Ty.nat ~> Ty.nat) :=
  let rec foo' (x : Γ Ty.nat) : Nat → Tm Γ Ty.nat
  | 0   => var x
  | n+1 => cst2 app (abs fun y => cst2 muln (var y) (var y)) (foo' x n)
  abs λ x => foo' x n
