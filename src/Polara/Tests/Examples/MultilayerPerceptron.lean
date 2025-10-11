import Polara.AD.All

-- https://en.wikipedia.org/wiki/Multilayer_perceptron

open Ty

def Ty.matrix: Nat → Nat → Ty → Ty := (Ty.array · <| Ty.array · ·)
notation:max ty"[["n"]]" => Ty.array n ty
notation:max ty"[["n","m"]]" => Ty.matrix n m ty

-- if' makes no norm faster norm slow, maxf makes no norm impossible
def Tm.relu (x: Term flt): Term flt := if' x <' tlitf 0 then tlitf 0 else x
-- def Tm.relu (x: Term flt): Term flt := x.maxf (tlitf 0)

def neuron {n: Nat} :=
  fun' x: flt[[n]] => fun' b: flt => fun' w: flt[[n]] =>
    (for' i => x[[i]] * w[[i]]).sumf + b |>.relu

def layer {n m: Nat} :=
 fun' x: flt[[n]] => fun' w: flt[[m]] ×× flt[[m,n]] =>
  for' i => (neuron @@ x @@ w.fst[[i]] @@ w.snd[[i]])

def layerLearnStep :=
  fun' x: flt[[20]] => fun' y: flt[[5]] =>
    fun' w: flt[[5]] ×× flt[[5, 20]] =>
      let' md :=(@layer 20 5 @@ x).dr.le;
      let't _, d := md @@ w;
      d @@ y

def multilayerPerceptron :=
  fun' x =>
    fun' ws: (flt[[10]] ×× flt[[10, 20]]) ×× (flt[[5]] ×× flt[[5, 10]]) =>
      let't w, ws := ws;
      let' x := layer @@ x @@ w;
      let' w := ws;
      let' x := layer @@ x @@ w;
      x

def learnStep :=
  fun' x: flt[[20]] => fun' y: flt[[5]] =>
    fun' ws: (flt[[10]] ×× flt[[10, 20]]) ×× (flt[[5]] ×× flt[[5, 10]]) =>
      (
        (multilayerPerceptron.dr.le.normVPar @@ x).fst @@ ws
      ).snd @@ y

#eval multilayerPerceptron
#eval multilayerPerceptron.dr.le --.normVPar
#eval learnStep @@ (for' x => tlitf 0) @@ (for' y => tlitf 1) @@ (Tm.zero _) |>.toVPar


-- def learnStep :=
--   fun' x: flt[[20]] => fun' y: flt[[5]] =>
--     fun' ws: (flt[[10]] ×× flt[[10, 20]]) ×× (flt[[5]] ×× flt[[5, 10]]) =>
--       (
--         (multilayerPerceptron @@ x).dr.le.normVPar @@ ws -- the x comes from the outside, which is forbidden
--       ).snd @@ y

#eval (fun'v x:flt => Tm.var (x.changeType: VPar nat)).normVPar -- normVPar checks types
