import Polara.AD.All

-- https://en.wikipedia.org/wiki/Multilayer_perceptron

open Ty

def Ty.matrix: Nat → Nat → Ty → Ty := (Ty.array · <| Ty.array · ·)
notation:max ty"[["n"]]" => Ty.array n ty
notation:max ty"[["n","m"]]" => Ty.matrix n m ty

def Tm.relu (x: Term flt): Term flt := x.maxf (tlitf 0)

def neuron {n: Nat}: Term (flt[[n]] ~> flt[[n]] ~> flt) :=
  fun' x => fun' w =>
    (for' i => x[[i]] * w[[i]]).sumf.relu

def layer {n m: Nat}: Term (flt[[n]] ~> flt[[m,n]] ~> flt[[m]]) :=
 fun' x => fun' w =>
  for' i => (neuron @@ x @@ w[[i]])

def layerLearn :=
  fun' x: flt[[100]] => fun' y: flt[[10]] =>
    fun' w: flt[[10, 100]] =>
      let' md :=(@layer 100 10 @@ x).dr.le;
      let't _, d := md @@ w;
      d @@ y

def multilayerPerceptron: Term <| flt[[100]] ~> flt[[50, 100]] ~> flt[[10, 50]] ~> flt[[10]] :=
  fun' x =>
    fun' w: flt[[50, 100]] =>
      let' x := layer @@ x @@ w;
    fun' w: flt[[10, 50]] =>
      let' x := layer @@ x @@ w;
      x

def learn: Term (flt.array 100 ~> flt.array 10 ~> flt.matrix 50 100 ~> flt.matrix 10 50 ~> (flt.matrix 50 100 ×× flt.matrix 10 50)) :=
  fun' x: flt[[100]] => fun' y: flt[[10]] =>
    fun' w1: flt[[50, 100]] =>
    fun' w2: flt[[10, 50]] =>
      let' md :=(multilayerPerceptron @@ x).dr.le;
      let't md, d1 := md @@ w1;
      let't _, d2 := md @@ w2;
      (d1 @@ (w2,, y),, d2 @@ y)


-- #eval (flt[[50,100]] ~> flt[[10,50]] ~> flt[[10]]).dr

-- structure Layers where
--   x: Nat
--   hidden: List Nat
--   y: Nat

-- @[reducible]
-- def Layers.weightsTy': Nat → Nat → List Nat → Ty
-- | n, m, []        => (flt.matrix m n)
-- | n, m, k :: rest => (flt.matrix m n) ×× (weightsTy' m k rest)

-- @[reducible]
-- def Layers.weightsTy (ls: Layers): Ty :=
--   match ls.hidden with
--   | []          => weightsTy' ls.x ls.y []
--   | k :: hidden => weightsTy' ls.x k (hidden.concat ls.y)

-- def multilayerPerceptron (ls: Layers): Term (flt.array ls.x ~> ls.weightsTy ~> flt.array ls.y) :=
--   fun' x =>
--     fun' w =>
--       layer @@ x @@ Tm.err
--   -- Tm.err


-- -- def multilayerPerceptron {n m: Nat}(hiddenLayers: List Nat): Term (flt.array n ~> flt.array m) :=
-- --   match hiddenLayers with
-- --   | [] => layer
-- --   | k :: hiddenLayers => Tm.err
