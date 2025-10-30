import Polara.AD.All
import Polara.Codegeneration.All

open Ty

def Tm.relu (x: Term flt): Term flt := x.maxf (tlitf 0)

namespace MultilayerPerceptron

  def loss {m: Pos} (y eY: Term flt[[m]]):=
    let' diff := (y - eY); diff * diff
  def learnRate: Term flt := tlitf (0.001)

  def neuron {n: Pos} (x: Term flt[[n]])(b: Term flt)(w: Term flt[[n]]):=
    (x * w).sumf + b |>.relu

  -- -- #eval neuron (n:=10) |>.normVPar
  -- def exampleNeuron := @neuron 2
  --   @@ (for' i:2 => tlitf 1)
  --   @@ Tm.zero _
  --   @@ Tm.zero _
  -- #eval run "Python" exampleNeuron "exampleNeuron"

  -- def neuronLearnStep {n: Pos} :=
  --   (fun' x: flt[[n]] => fun' y:flt =>
  --     fun' w: flt ×× flt[[n]] =>
  --       let' t := (fun' w: flt ×× flt[[n]] =>
  --           loss
  --           @@ (for' i:1 => (@neuron n @@ x @@ w.fst @@ w.snd))
  --           @@ (for' i:1 => y)
  --         ).dr.le;
  --       let't _, d := t @@ w;
  --       let' d := (d @@ (for' i:1 => tlitf 1));
  --       (w.fst + learnRate*d.fst,, w.snd + for' i => learnRate*d.snd[[i]])
  --   ).normVPar
  -- def exampleNeuronLearnStep := @neuronLearnStep 2
  --   @@ (for' i:2 => tlitf 1)
  --   @@ (tlitf 1)
  --   @@ Tm.one _
  -- #eval run "Python" exampleNeuronLearnStep "exampleNeuronLearnStep"

  def layer {n m: Pos} (x: Term flt[[n]])(w: Term (flt[[m]] ×× flt[[m,n]])):=
    for' i => (neuron x w.fst[[i]] w.snd[[i]])

  -- #eval (@layer 10 5) |>.normVPar

  def Weights (n k m: Pos) := (flt[[k]] ×× flt[[k, n]]) ×× (flt[[m]] ×× flt[[m, k]])

  def Weights.weightedSum (a: Term (Weights n k m))(w: Term flt)(b: Term (Weights n k m)): Term (Weights n k m) :=
    -- a + wb
    ((for' i => a.fst.fst[[i]] + w*b.fst.fst[[i]],,
      for' i => for' j => a.fst.snd[[i]][[j]] + w*b.fst.snd[[i]][[j]]),,
    (for' i => a.snd.fst[[i]] + w*b.snd.fst[[i]],,
      for' i => for' j => a.snd.snd[[i]][[j]] + w*b.snd.snd[[i]][[j]]))

  def multilayerPerceptron {n k m: Pos} :=
    (
      fun' x:flt[[n]] =>
        fun' ws: Weights n k m =>
          let' x := layer x ws.fst;
          let' x := layer x ws.snd;
          x
    ).normVPar

  -- #eval @multilayerPerceptron 10 5 1

  def learnStep {n k m: Pos} :=
    (fun' x: flt[[n]] => fun' y: flt[[m]] =>
      fun' ws: Weights n k m =>
        Weights.weightedSum
          ws
          learnRate.neg
          (
            let't _,d := (
              fun' ws => loss (multilayerPerceptron @@ x @@ ws) y
            ).dr.le @@ ws;
            d @@ (for' i => tlitf 1)
          )
    ).normVPar

  -- #eval (@learnStep 5 2 1).normVPar

  def exampleOrLearnStep := (@learnStep 2 1 1)
        @@ (for' x => tlitf 1)
        @@ (for' y => tlitf 4)
        @@ ((for' i:1 => tlitf (0),, for' i:1 => #[tlitf (1), tlitf (1)].toTm 2),,
            (for' i:1 => tlitf (0),, for' i:1 => for' j:1 => tlitf (1) ))
        |>.normVPar

  -- #eval run "Python" exampleOrLearnStep "exampleOrTestLearnSTep"

  def learn {n k m l: Pos} :=
    (fun' x: flt[[n]][[l]] => fun' y: flt[[m]][[l]] =>
      fun' ws: Weights n k m =>
        (for' i:l => i).foldA
          (fun' i => fun' ws => learnStep @@ x[[i]] @@ y[[i]] @@ ws)
          ws
    ).normVPar

  -- #eval (@learn 2 1 1 4) |>.normVPar

  def exampleOr := (@learn 2 1 1 16)
        @@ (#[
            #[tlitf 1, tlitf 1].toVector.toTm,
            #[tlitf 1, tlitf 1].toVector.toTm,
            #[tlitf 5, tlitf 1].toVector.toTm,
            #[tlitf 1, tlitf 10].toVector.toTm,
            #[tlitf 5, tlitf 5].toVector.toTm,
            #[tlitf 1, tlitf 1].toVector.toTm,
            #[tlitf 10, tlitf 1].toVector.toTm,
            #[tlitf 10, tlitf 1].toVector.toTm,
            #[tlitf 1, tlitf 1].toVector.toTm,
            #[tlitf 1, tlitf 1].toVector.toTm,
            #[tlitf 5, tlitf 1].toVector.toTm,
            #[tlitf 1, tlitf 10].toVector.toTm,
            #[tlitf 5, tlitf 5].toVector.toTm,
            #[tlitf 1, tlitf 1].toVector.toTm,
            #[tlitf 10, tlitf 1].toVector.toTm,
            #[tlitf 10, tlitf 1].toVector.toTm,
          ].toVector.toTm)
        @@ (#[
            #[tlitf 2].toVector.toTm,
            #[tlitf 2].toVector.toTm,
            #[tlitf 6].toVector.toTm,
            #[tlitf 11].toVector.toTm,
            #[tlitf 10].toVector.toTm,
            #[tlitf 2].toVector.toTm,
            #[tlitf 11].toVector.toTm,
            #[tlitf 11].toVector.toTm,
            #[tlitf 2].toVector.toTm,
            #[tlitf 2].toVector.toTm,
            #[tlitf 6].toVector.toTm,
            #[tlitf 11].toVector.toTm,
            #[tlitf 10].toVector.toTm,
            #[tlitf 2].toVector.toTm,
            #[tlitf 11].toVector.toTm,
            #[tlitf 11].toVector.toTm,
          ].toVector.toTm)
        @@ ((for' i:1 => tlitf (0),, for' i:1 => #[tlitf (0.3), tlitf (1)].toTm 2),,
            (for' i:1 => tlitf (0),, for' i:1 => for' j:1 => tlitf (3) ))
        |>.normVPar

  -- #eval exampleOr
  -- #eval run "Python" exampleOr "exampleOr"

  def exampleOrTest := (multilayerPerceptron
        @@ #[tlitf 2, tlitf 3].toTm 2
        @@ exampleOr)
        -- @@ ((for' i:1 => tlitf (0),, for' i:1 => #[tlitf (1), tlitf (1)].toTm 2),,
        --     (for' i:1 => tlitf (0),, for' i:1 => for' j:1 => tlitf (1) ))

  -- #eval exampleOrTest
  -- #eval run "Python" BenchRes.test (exampleOrTest.normVPar) "multilayerPerceptron/exampleOrTest"

end MultilayerPerceptron
