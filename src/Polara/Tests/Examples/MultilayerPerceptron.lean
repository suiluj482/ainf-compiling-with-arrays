import Polara.AD.All

-- https://en.wikipedia.org/wiki/Multilayer_perceptron

open Ty

def Ty.matrix: Nat → Nat → Ty → Ty := (Ty.array · <| Ty.array · ·)
notation:max ty"[["n"]]" => Ty.array n ty
notation:max ty"[["n","m"]]" => Ty.matrix n m ty

-- if' makes no norm faster norm slow, maxf makes no norm impossible
-- def Tm.relu (x: Term flt): Term flt := if' x <' tlitf 0 then tlitf 0 else x
def Tm.relu (x: Term flt): Term flt := x.maxf (tlitf 0)

def loss {m: Nat} :=
  fun' y:flt[[m]] => fun' eY:flt[[m]] =>
    let' diff := (y - eY); diff * diff
    |>.toVPar

#eval loss (m:=10) |>.normVPar

def neuron {n: Nat} :=
  fun' x: flt[[n]] => fun' b: flt => fun' w: flt[[n]] =>
    (x * w).sumf + b |>.relu

#eval neuron (n:=10) |>.normVPar

def layer {n m: Nat} :=
 fun' x: flt[[n]] => fun' w: flt[[m]] ×× flt[[m,n]] =>
  for' i => (neuron @@ x @@ w.fst[[i]] @@ w.snd[[i]])

#eval (@layer 10 5) |>.normVPar

-- def layerLearnStep :=
--   fun' x: flt[[20]] => fun' y: flt[[5]] =>
--     fun' w: flt[[5]] ×× flt[[5, 20]] =>
--       let' md :=(@layer 20 5 @@ x).dr.le;
--       let't _, d := md @@ w;
--       d @@ y


def Weights (n k m: Nat) := (flt[[k]] ×× flt[[k, n]]) ×× (flt[[m]] ×× flt[[m, k]])

def multilayerPerceptron {n k m: Nat} :=
  fun' x:flt[[n]] =>
    fun' ws: Weights n k m =>
      let x := layer @@ x @@ ws.fst;
      let x := layer @@ x @@ ws.snd;
      x

#eval @multilayerPerceptron 10 5 1 |>.normVPar

def learnStep {n k m: Nat} :=
  fun' x: flt[[n]] => fun' y: flt[[m]] =>
    fun' ws: Weights n k m =>
      (
        (fun' ws => loss @@ (multilayerPerceptron @@ x @@ ws) @@ y).normVPar.dr.le.normVPar @@ ws
      ).snd @@ y

#eval @multilayerPerceptron 10 5 1 |>.normVPar.dr.le.normVPar
#eval (@learnStep 5 2 1) @@ (for' x => tlitf 0) @@ (for' y => tlitf 1) @@ (Tm.zero _) |>.toVPar

def x := (for' x:10 => tlitf 0) |>.toVPar
def y := (for' y:1 => tlitf 1) |>.toVPar

#eval fun' ws: Weights 10 5 1 =>
  (fun' ws:Weights 10 5 1 => loss @@ (multilayerPerceptron @@ x @@ ws) @@ y).normVPar.dr.le.normVPar
  @@ ws -- |>.normVPar
