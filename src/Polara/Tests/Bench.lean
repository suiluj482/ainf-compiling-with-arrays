import Polara.Tests.All

open Tree Ty MultilayerPerceptron Tm

private def tree: TmTree :=
    node "Bench" [
      node "MultilayerPerceptron" [
        leaf ⟨"run", _,_,
          @multilayerPerceptron 2 1 1,
          (λ t => t
            -- inputs
            @@ (for' j => if' j.eqi (tliti 0) then tlitf 0 else tlitf 1)
            -- start weights
            @@ ((for' i:1 => tlitf (0),, for' i:1 => #[tlitf (1), tlitf (1)].toTm 2),,
                (for' i:1 => tlitf (0),, for' i:1 => for' j:1 => tlitf (1) ))
          ),
          some (#[1].toVector)
        ⟩,
        leaf ⟨"learnStep", _,_,
          @learnStep 2 1 1,
          (λ t => t
            -- inputs
            @@ (for' j => if' j.eqi (tliti 0) then tlitf 0 else tlitf 1)
            -- outputs
            @@ (for' j => tlitf 1)
            -- start weights
            @@ ((for' i:1 => tlitf (0),, for' i:1 => #[tlitf (1), tlitf (1)].toTm 2),,
                (for' i:1 => tlitf (0),, for' i:1 => for' j:1 => tlitf (1) ))
          ),
          none
        ⟩,
        -- leaf ⟨"learn", _,_,
        --   @learn 2 1 1 8,
        --   (λ t => t
        --     -- inputs
        --     @@ (for' i =>
        --         let' i := i.i2n.n2f;
        --         for' j => if' j.eqi (tliti 0) then i else tlitf 8-i)
        --     -- outputs
        --     @@ (for' i => for' j => tlitf 8)
        --     -- start weights
        --     @@ ((for' i:1 => tlitf (0),, for' i:1 => #[tlitf (1), tlitf (1)].toTm 2),,
        --         (for' i:1 => tlitf (0),, for' i:1 => for' j:1 => tlitf (1) ))
        --   ),
        --   none
        -- ⟩,
      ],
    ]

def main: IO Unit :=
  TmTest.print tree BenchRes.bench
