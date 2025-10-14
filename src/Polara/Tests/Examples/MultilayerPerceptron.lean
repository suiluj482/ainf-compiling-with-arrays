import Polara.AD.All

-- https://en.wikipedia.org/wiki/Multilayer_perceptron

open Ty

def Tm.relu (x: Term flt): Term flt := x.maxf (tlitf 0)

def loss {m: Pos} :=
  fun' y:flt[[m]] => fun' eY:flt[[m]] =>
    let' diff := (y - eY); diff * diff
    |>.toVPar

-- #eval loss (m:=10) |>.normVPar

def neuron {n: Pos} :=
  fun' x: flt[[n]] => fun' b: flt => fun' w: flt[[n]] =>
    (x * w).sumf + b |>.relu

-- #eval neuron (n:=10) |>.normVPar

def layer {n m: Pos} :=
 fun' x: flt[[n]] => fun' w: flt[[m]] ×× flt[[m,n]] =>
  for' i => (neuron @@ x @@ w.fst[[i]] @@ w.snd[[i]])

-- #eval (@layer 10 5) |>.normVPar

def Weights (n k m: Pos) := (flt[[k]] ×× flt[[k, n]]) ×× (flt[[m]] ×× flt[[m, k]])

def multilayerPerceptron {n k m: Pos} :=
  fun' x:flt[[n]] =>
    fun' ws: Weights n k m =>
      let x := layer @@ x @@ ws.fst;
      let x := layer @@ x @@ ws.snd;
      x

-- #eval @multilayerPerceptron 10 5 1 |>.normVPar

def learnStep {n k m: Pos} :=
  fun' x: flt[[n]] => fun' y: flt[[m]] =>
    fun' ws: Weights n k m =>
      (
        (fun' ws => loss @@ (multilayerPerceptron @@ x @@ ws) @@ y).dr.le @@ ws
      ).snd @@ y

-- #eval @multilayerPerceptron 10 5 1 |>.normVPar.dr.le.normVPar
-- #eval (@learnStep 5 2 1) @@ (for' x => tlitf 0) @@ (for' y => tlitf 1) @@ (Tm.zero _) --|>.normVPar
