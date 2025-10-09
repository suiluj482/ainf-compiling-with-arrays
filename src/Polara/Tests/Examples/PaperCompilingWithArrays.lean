import Polara.Optimizations.All

open Tm Ty

------------------------------------------------------------------------------------------
-- Black scholes
------------------------------------------------------------------------------------------

def calls: Tm Γ (flt ~> flt ~> flt ~> flt ~> flt ~> flt) :=
  fun' S => fun' K => fun' T => fun' r => fun' sigma =>
  let' d1 := ((S.log / K + (r + sigma * sigma / tlitf 2) * T) / sigma * T.sqrt);
  let' d2 := d1 - sigma * T.sqrt;
  S * normCdf d1 - K * (exp (tlitf 0 - r * T)) * normCdf d2

def puts: Tm Γ (flt ~> flt ~> flt ~> flt ~> flt ~> flt) :=
  fun' S => fun' K => fun' T => fun' r => fun' sigma =>
  let' d1 := ((S.log / K + (r + sigma * sigma / tlitf 2) * T) / sigma * T.sqrt);
  let' d2 := d1 - sigma * T.sqrt;
  K * (tlitf 0 - r * T).exp * (tlitf 0 - d2).normCdf - S * (tlitf 0 - d1).normCdf

def mainBlackScholes : Tm Γ (array n flt ~> array n (flt ×× flt)) :=
  fun' arr =>
  let' S := (tlitf 1);
  let' K := (tlitf 1);
  let' r := (tlitf 1);
  let' sigma := (tlitf 1);
  let' Calls := (for' i => calls @@ S @@ K @@ arr[[i]] @@ r @@ sigma);
  let' Puts := (for' i => puts @@ S @@ K @@ arr[[i]] @@ r @@ sigma);
  for' i => (Calls[[i]],, Puts[[i]])

-- #eval (Tm.norm (mainBlackScholes (Γ:=.) (n:=1))).toAINF
-- #eval (Tm.norm (mainBlackScholes (Γ:=.) (n:=10))).toAINF.cse

------------------------------------------------------------------------------------------
-- dense example
------------------------------------------------------------------------------------------

-- dense(b: [n]Float, W: [n,m]Float, x: [m]Float) :=
  -- for i. max(0, (sum j. W[i,j] * x[j]) + b[i])

def dense {Γ : Ty → Type} n m : Tm Γ (
  array n flt ~> array n (array m flt) ~> array m flt ~> array n flt
) :=
  fun' b => fun' W => fun' x =>
    for' i => (tlitf 0).maxf ((for' j => W[[i]][[j]] * x[[j]]).sumf + b[[i]])

------------------------------------------------------------------------------------------
-- conv example
------------------------------------------------------------------------------------------

-- conv(x: [n]Float, y: [m]Float) : [n+m−1]Float :=
  -- for i. sum j. x[j] * y[i+j]

def conv {Γ : Ty → Type} n m : Tm Γ (
  array n flt ~> array (n+m) flt ~> array m flt
) :=
  fun' x => fun' y =>
    for' i =>
      (for' j => x[[j]] * y[[j.addi i]]).sumf

------------------------------------------------------------------------------------------
-- CSE test for loop
------------------------------------------------------------------------------------------

def loop1 {Γ : Ty → Type} n : Tm Γ ((array n nat) ×× (array n nat)) :=
  let' l0 := (for' _i =>
      let' t := (tlitn n);
      t + (tlitn 1)
    );
  let' l1 := (for' _i =>
      let' t:= (tlitn n);
      t * (tlitn 2)
    );
  (l0,, l1)

def incr (t : Tm Γ nat) : Tm Γ nat :=
  t + (tlitn 1)

--x = for i.
-- ys = f(xs[i])
-- zs = f(xs[i])
-- (ys,zs)
--(for i: fst x[i])
def foo : Tm Γ (array n nat ~> array n nat) :=
  fun' xs =>
    let' x := for' i => (incr xs[[i]],,incr xs[[i]]);
    for' i => x[[i]].fst

------------------------------------------------------------------------------------------
-- CSE test for if-then-else
------------------------------------------------------------------------------------------

-- partial redundancy test
def cseTest1 {Γ : Ty → Type} : Tm Γ (Ty.nat ~> Ty.nat) :=
  fun' x => -- 1+x should be shared across the branches
    if' x
      then (tlitn 42) + (tlitn 1) + x
      else (tlitn 24) + (tlitn 1) + x

-- #eval cseTest1.toAINF

def cseTest2 {Γ : Ty → Type} : Tm Γ (Ty.nat ~> Ty.nat) :=
  fun' x => -- 1+x should be shared across the beginning and the branch
    let' _l0 := (tlitn 1) + x;
    if' x
      then x
      else (tlitn 1) + x

-- #eval cseTest2.toAINF

def cseTest3 {Γ : Ty → Type} : Tm Γ (Ty.nat ~> Ty.nat) :=
  fun' x => -- 1+x should be shared across the branch and the end
    let' _l0 := if' x then x else (tlitn 1) + x;
    (tlitn 1) + x

-- #eval cseTest3.toAINF

------------------------------------------------------------------------------------------
-- PE & CSE test
------------------------------------------------------------------------------------------

def egyptLean (n: Nat) (x: Nat) :=
  n ^ (2 ^ x)

def egypt (n: Nat) {Γ : Ty → Type} : Tm Γ (Ty.nat ~> Ty.nat) :=
  let rec foo' (x : Tm Γ Ty.nat) : Nat → Tm Γ Ty.nat
  | 0   => x
  | n+1 => (fun' y => y * y) @@ (foo' x n)
  fun' x => foo' x n
