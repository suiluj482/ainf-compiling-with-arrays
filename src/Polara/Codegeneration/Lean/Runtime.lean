-- hilfsmethoden für generierten lean code
def Array.ebuild (n: Nat) (f: Fin n → Except String α): Except String (Array α) :=
  have tmp: (mkArray n 0).size = n := by simp [mkArray, Array.size]
  ((mkArray n 0).mapIdx fun i _x => f (tmp▸i)).mapM fun i => i

#check (mkArray 10 0)
#eval (10: Fin 10)

class Monoid (α: Type) where
  default : α
  combine : α → α → α

instance : Monoid Nat where
  default := 0
  combine := (. + .)

instance : Monoid Float where
  default := 0
  combine := (. + .)

def Array.esum [Inhabited α] [Monoid α]: Nat → (Array α) → α
| n, f => ((mkArray n 0).mapIdx fun i _x => f.get! i).foldl Monoid.combine Monoid.default

-- kein clock überlauf
def Fin.add' : Fin n → Fin m → Fin (n+m-1)
| ⟨x, hx⟩, ⟨y, hy⟩ => ⟨x+y,
  let ⟨ x', hx' ⟩ := Nat.le.dest hx;
  let ⟨ y', hy' ⟩ := Nat.le.dest hy;
  Nat.le.intro (k := x' + y') (by simp_arith! [←hx', ←hy']) ⟩

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
