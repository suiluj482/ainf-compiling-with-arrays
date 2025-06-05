import Polara.Codegeneration.Index
import Polara.Tests.Utils

namespace AinfTestCases

  open Notations Ty Const0 Const1 Const2 Prim AINF EnvPart

  def ainfSimpleTestCases : List (TestCase (Some AINF)) := [
    -- cst0
    ⟨"litn", Ty.nat,
        let'' [] in x0 := plitn 42;
        .ret (.v x0)
    ⟩,
    ⟨"litf", Ty.flt,
        let'' [] in x0 := plitf 4.2;
        .ret (.v x0)
    ⟩,
    ⟨"liti", idx 5,
        let'' [] in (x0: Var (idx 5)) := Prim.cst0 (liti (2: Fin 6));
        .ret (.v x0)
    ⟩,
    -- cst1
    ⟨"exp", flt,
        let'' [] in x0 := plitf 4.2;
        let'' [] in x1 := cst1 exp (.v x0);
        .ret (.v x1)
    ⟩,
    ⟨"sqrt", flt,
        let'' [] in x0 := plitf 4.2;
        let'' [] in x1 := cst1 sqrt (.v x0);
        .ret (.v x1)
    ⟩,
    ⟨"log", flt,
        let'' [] in x0 := plitf 4.2;
        let'' [] in x1 := cst1 log (.v x0);
        .ret (.v x1)
    ⟩,
    ⟨"normCdf", flt,
        let'' [] in x0 := plitf 4.2;
        let'' [] in x1 := cst1 normCdf (.v x0);
        .ret (.v x1)
    ⟩,
    ⟨"fst", flt,
        let x0: Var _ := (Var.mk 0)
        let x1: Var _ := x1
        let x2: Var _ := x2
        let x3: Var _ := x3
        let'' [] in x0 := plitf 4.2;
        let'' [] in x1 := plitn 42;
        let'' [] in x2 := cst2 tup (.v x0) (.v x1);
        let'' [] in x3 := cst1 fst (.v x2);
        .ret (.v x3)
    ⟩,
    ⟨"snd", nat,
        let'' [] in x0 := plitf 4.2;
        let'' [] in x1 := plitn 42;
        let'' [] in x2 := cst2 tup (.v (@x0 flt)) (.v (@x1 nat));
        let'' [] in x3 := cst1 snd (.v (x2: Var (flt ×× nat)));
        .ret (.v x3)
    ⟩,
    ⟨"sum", nat, -- todo only nat or flt
        let'' [] in x0 := plitn 42;
        let'' [] in x1 := for'' i0:10, (.v (x0: Var nat));
        let'' [] in x2 := cst1 sum (.v (x1: Var (array 10 nat)));
        .ret (.v x2)
    ⟩,
    ⟨"i2n", nat,
        let'' [] in (x0: Var (idx 5)) := Prim.cst0 (liti (2: Fin 6));
        let'' [] in x1 := cst1 i2n (.v (x0: Var (idx 5)));
        .ret (.v x1)
    ⟩,
    ⟨"n2f", flt,
        let'' [] in x0 := plitn 42;
        let'' [] in x1 := cst1 n2f (.v (x0: Var nat));
        .ret (.v x1)
    ⟩,
    -- cst2
    ⟨"addn", nat,
        let'' [] in x0 := plitn 42;
        let'' [] in x1 := plitn 2;
        let'' [] in x2 := cst2 addn (.v (x0: Var nat)) (.v (x1: Var nat));
        .ret (.v x2)
    ⟩,
    ⟨"muln", nat,
        let'' [] in x0 := plitn 42;
        let'' [] in x1 := plitn 2;
        let'' [] in x2 := cst2 muln (.v (x0: Var nat)) (.v (x1: Var nat));
        .ret (.v x2)
    ⟩,
    ⟨"addf", flt,
        let'' [] in x0 := plitf 42.0;
        let'' [] in x1 := plitf 2.0;
        let'' [] in x2 := cst2 addf (.v (x0: Var flt)) (.v (x1: Var flt));
        .ret (.v x2)
    ⟩,
    ⟨"subf", flt,
        let'' [] in x0 := plitf 42.0;
        let'' [] in x1 := plitf 2.0;
        let'' [] in x2 := cst2 subf (.v (x0: Var flt)) (.v (x1: Var flt));
        .ret (.v x2)
    ⟩,
    ⟨"mulf", flt,
        let'' [] in x0 := plitf 42.0;
        let'' [] in x1 := plitf 2.0;
        let'' [] in x2 := cst2 mulf (.v (x0: Var flt)) (.v (x1: Var flt));
        .ret (.v x2)
    ⟩,
    ⟨"divf", flt,
        let'' [] in x0 := plitf 42.0;
        let'' [] in x1 := plitf 2.0;
        let'' [] in x2 := cst2 divf (.v (x0: Var flt)) (.v (x1: Var flt));
        .ret (.v x2)
    ⟩,
    ⟨"maxf", flt,
        let'' [] in x0 := plitf 42.0;
        let'' [] in x1 := plitf 2.0;
        let'' [] in x2 := cst2 maxf (.v (x0: Var flt)) (.v (x1: Var flt));
        .ret (.v x2)
    ⟩,
    ⟨"addi", idx 10,
        let'' [] in (x0: Var (idx 5)) := Prim.cst0 (liti (2: Fin 6));
        let'' [] in (x1: Var (idx 5)) := Prim.cst0 (liti (2: Fin 6));
        let'' [] in x2 := cst2 addi (.v (x0: Var (idx 5))) (.v (x1: Var (idx 5)));
        .ret (.v x2)
    ⟩,
    ⟨"get", flt,
        let'' [] in x0 := plitf 4.2;
        let'' [] in x1 := for'' i0:10, (.v (x0: Var flt));
        let'' [] in (x2: Var (idx 10)) := cst0 (liti (2: Fin 11));
        let'' [] in x3 := cst2 get (.v (x1: Var (array 10 flt))) (.v (x2: Var (idx 10)));
        .ret (.v x3)
    ⟩,
    ⟨"tup", flt ×× nat,
        let'' [] in x0 := plitf 4.2;
        let'' [] in x1 := plitn 42;
        let'' [] in x2 := cst2 tup (.v (x0: Var flt)) (.v (x1: Var nat));
        .ret (.v x2)
    ⟩,
    ⟨"app", flt,
        let'' [] in x0 := plitf 4.2;
        let'' [] in x1 := fun'' (i0: Par nat), (.v (x0: Var flt));
        let'' [] in (x2: Var nat) := plitn 42;
        let'' [] in x3 := cst2 app (.v (x1: Var (nat ~> flt))) (.v (x2: Var nat));
        .ret (.v x3)
    ⟩,
    -- prim
    ⟨"var", nat,
        let'' [] in x0 := plitn 42;
        let'' [] in x1 := Prim.var (.v (x0: Var nat));
        .ret (.v x1)
    ⟩,
    ⟨"abs", flt,
        let'' [] in x0 := plitf 4.2;
        let'' [] in x1 := fun'' (i0: Par nat), (.v (x0: Var flt));
        -- app because function can't be printed
        let'' [] in (x2: Var nat) := plitn 42;
        let'' [] in x3 := cst2 app (.v (x1: Var (nat ~> flt))) (.v (x2: Var nat));
        .ret (.v x3)
    ⟩,
    ⟨"bld", array 10 flt,
        let'' [] in x0 := plitf 4.2;
        let'' [] in x1 := for'' i0:10, (.v (x0: Var flt));
        .ret (.v x1)
    ⟩,
    ⟨"ite", flt,
        let'' [] in x0 := plitn 42;
        let'' [] in x1 := plitf 4.2;
        let'' [] in x2 := plitf 2.4;
        let'' [] in x3 := if'' (.v (x0: Var nat)) then (.v (x1: Var flt)) else (.v (x2: Var flt));
        .ret (.v x3)
    ⟩,
    -- more complex
    ⟨"vectorRange", array 10 flt,
        let'' [forc 10 i0] in x0 := cst1 i2n (.p (i0: Par (idx 10)));
        let'' [forc 10 i0] in x1 := cst1 n2f (.v (x0: Var nat));
        let'' [] in x2 := for'' i0:10, (.v (x1: Var flt));
        .ret (.v x2)
        -- let'' [forc 10 i0] in x0 := cst1 n2f (.p (i0: Par nat));
        -- let'' [] in x1 := for'' i0:10, (.v (x0: Var flt));
        -- .ret (.v x1)
    ⟩,
  ]

  ------------------------------------------------------------------------------------------
  -- Invalid AINF
  ------------------------------------------------------------------------------------------
  def ainfInvalidTestCases: List (TestCase (Some AINF)) := [
    ⟨"nonExistingVar", nat,
      .ret (.v x0)
    ⟩,
    ⟨"wrongVarType", flt,
      let'' [] in x0 := plitn 42;
      .ret (.v x1)
    ⟩,
    ⟨"nonEmptyReturnEnv", array 10 flt,
      let'' [forc 10 i0] in x0 := plitf 4.2;
      .ret (.v x0)
    ⟩,
    ⟨"incompatibleEnvFor", flt,
      let'' [forc 10 i0] in x0 := plitf 4.2;
      let'' [] in x1 := var (.v (x0: Var flt));
      .ret (.v x1)
    ⟩,
    ⟨"incompatibleEnvFun", flt,
      let'' [func nat i0] in x0 := plitf 4.2;
      let'' [] in x1 := var (.v (x0: Var flt));
      .ret (.v x1)
    ⟩,
    ⟨"incompatibleEnvIf", flt,
      let'' [] in x0 := plitn 42;
      let'' [itec (.v x0: VPar nat) true] in x1 := plitf 4.2;
      let'' [] in x2 := var (.v (x0: Var flt));
      .ret (.v x2)
    ⟩,
    ⟨"multipleDefinitionsVar", flt,
      let'' [] in x0 := plitf 4.2;
      let'' [] in x0 := plitf 4.2;
      .ret (.v x0)
    ⟩,
    -- ...
  ]

  def runners: List (String × (Term α → IO String)) := [
    ("Lean", runLean ∘ Tm.codegen),
    ("Py",   runWithRuntime "Python" ∘ (s!"print({·})") ∘ Tm.codegenPy),
    ("Jax",  runWithRuntime "Jax"    ∘ (s!"print({·})") ∘ Tm.codegenJax),
  ]

  def runner: Runner (Some AINF) := λ ⟨α, a⟩ => do
    let tm: Term α := a.toTm
    let results ← runners.mapM (λ (n, run) => do
      let res ← run tm
      return (n, res)
    )
    return (
      "\n" ++ (results.map (λ (n, res) => s!"{n}: {res}") |>.foldl (λ acc x => s!"{acc}  | {x}") "" |>.dropRight 1),
      true -- todo compare res
    )


  def testCaseTree: TestCaseTree := Tree.node "ainf testcases"
    [
      Tree.leaf ("ainfSimpleTestCases",
        ⟨_, ainfSimpleTestCases, runner⟩
      ),
      Tree.leaf ("ainfInvalidTestCases",
        ⟨_, ainfInvalidTestCases, (λ ⟨_, a⟩ => pure ("", a.valid.not))⟩
      ),
    ]

--   #eval testCaseTree.print

end AinfTestCases
