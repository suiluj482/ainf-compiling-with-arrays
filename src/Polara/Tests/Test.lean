-- not upddated yet

-- import Polara.Examples.Definitions
-- import Lean
-- import Polara.Codegeneration.Lean.Runtime
-- import Polara.Codegeneration.Index

-- def evalStr (e : String) : IO String := runLean e
-- -- Utility for testing
-- initialize success : IO.Ref (Array String) ← IO.mkRef #[]
-- initialize failure : IO.Ref (Array String) ← IO.mkRef #[]
-- initialize testPrefix : IO.Ref String ← IO.mkRef ""

-- def group (p: String) (x: IO Unit) := do
--   testPrefix.set (s!"{p}."); x; testPrefix.set ""

-- def assert (name: String) (c: Bool) := do
--   let fullname := (← testPrefix.get) ++ name
--   if !c then
--     failure.modify (Array.push . fullname)
--     IO.println ("* ERROR " ++ fullname)
--   else
--     success.modify (Array.push . fullname)
--     IO.println ("* OK    " ++ fullname)

-- def printEq (a: String) (b: String): IO Unit := do
--   IO.print " "
--   if a.contains '\n' || b.contains '\n' then
--     IO.println "equals: "
--     IO.print "= "
--     IO.println (a.replace "\n" "\n  ")
--     IO.print "= "
--     IO.println (b.replace "\n" "\n  ")
--   else
--     IO.print "("
--     IO.print a
--     IO.print ") != ("
--     IO.print b
--     IO.println ")"

-- def assertEq (name: String) (a: String) (b: String) := do
--   let fullname := (← testPrefix.get) ++ name
--   if a != b then
--     failure.modify (Array.push . fullname)
--     IO.print ("* ERROR " ++ fullname)
--     printEq a b
--   else
--     success.modify (Array.push . fullname)
--     IO.println ("* OK    " ++ fullname)

-- infixl:65 " @@@ " => AINF.app'

-- -- #eval cseTest1 (Γ:=_).toAINF

-- -- Test suite
-- namespace Test
--   def toAINF : IO Unit := group "toAinf" <| do
--     let out := "  let fun i0:Nat, if i0!=0, (x0 : Nat := 42)
--   let fun i0:Nat, if i0!=0, (x1 : Nat := 1)
--   let fun i0:Nat, if i0!=0, (x2 : Nat := x1 + i0)
--   let fun i0:Nat, if i0!=0, (x3 : Nat := x0 + x2)
--   let fun i0:Nat, if i0==0, (x4 : Nat := 24)
--   let fun i0:Nat, if i0==0, (x5 : Nat := 1)
--   let fun i0:Nat, if i0==0, (x6 : Nat := x5 + i0)
--   let fun i0:Nat, if i0==0, (x7 : Nat := x4 + x6)
--   let fun i0:Nat, (x8 : Nat := if i0 != 0 then x3 else x7)
--   let (x9 : (Nat ~> Nat) := fun i0:Nat, x8)
-- x9"
--     assert "cseTest1: converted correctly" (out == cseTest1 (Γ:=_).toAINF.toString)

--   def CSE : IO Unit := group "CSE" do
--     let mut i := 0
--     for cseTest in #[cseTest1 (Γ:=VPar), cseTest2 (Γ:=VPar), cseTest3 (Γ:=VPar)] do
--       i := i+1
--       let pre1  := cseTest.toAINF
--       let post1 := cseTest.toAINF.cse
--       assert s!"cseTest{i}: size reduced" (post1.size < pre1.size)

--       let argS  := " 0"
--       let pre2  <- evalStr <| pre1.codegen  fun x => x ++ argS
--       let post2 <- evalStr <| post1.codegen fun x => x ++ argS
--       assertEq s!"cseTest{i}: equivalent" post2 pre2

--       let argS  := " 1"
--       let pre2  <- evalStr <| pre1.codegen  fun x => x ++ argS
--       let post2 <- evalStr <| post1.codegen fun x => x ++ argS
--       assertEq s!"cseTest{i}: equivalent" post2 pre2

--     let pre1  := (Tm.norm (mainBlackScholes (Γ:=.) (n:=1))).toAINF
--     let post1 := (Tm.norm (mainBlackScholes (Γ:=.) (n:=1))).toAINF.cse
--     IO.println (pre1.size, post1.size)
--     let argS  := " #[2.5]"
--     let pre2  <- evalStr <| pre1.codegen  fun x => x ++ argS
--     let post2 <- evalStr <| post1.codegen fun x => x ++ argS
--     assert "normalized BlackScholes: size reduced" (post1.size < pre1.size)
--     assertEq s!"normalized BlackScholes: equivalent" post2 pre2

--     let pre1  := ((mainBlackScholes (Γ:=_) (n:=1))).toAINF
--     let post1 := ((mainBlackScholes (Γ:=_) (n:=1))).toAINF.cse
--     IO.println (pre1.size, post1.size)
--     let argS  := " #[2.5]"
--     let pre2  <- evalStr <| pre1.codegen  fun x => x ++ argS
--     let post2 <- evalStr <| post1.codegen fun x => x ++ argS
--     assert "BlackScholes: size reduced" (post1.size < pre1.size)
--     assertEq s!"BlackScholes: equivalent" post2 pre2

--   def codegen : IO Unit := group "codegen" <| do
--     let base := 7
--     let expo := 13

--     let e1 := (Tm.norm (fun _ => Tm.cst2 Const2.app (egypt base) (.cst0 (.litn expo)))).toAINF.cse |>.codegen id
--     let e2 := (Tm.norm (fun _ => (egypt base))).toAINF.cse |>.codegen fun x => x ++ s!" {expo}"
--     let actual1 ← evalStr e1
--     let actual2 ← evalStr e2
--     let expected := egyptLean expo base
--     IO.println <| "asdf:" ++ e1
--     IO.println <| "asdf:" ++ actual2
--     IO.println <| "asdf:" ++ s!"{expected}"
--     assertEq "egypt: generated code evaluates correctly" actual1.trim s!"{expected}"
--     assertEq "egypt: generated code evaluates correctly" actual2.trim s!"ok: {expected}"

-- end Test

-- def main := do
--   IO.println ""
--   IO.println "Running tests"
--   Test.codegen
--   Test.toAINF
--   Test.CSE
--   let total := (← success.get).size + (← failure.get).size
--   IO.println s!"=== {(← success.get).size} / {total} tests passed"

--   -- IO.println "failure messages"
--   -- for x in ← failure.get do IO.println s!"{x} "
--   -- IO.println "==="
