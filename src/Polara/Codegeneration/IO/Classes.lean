open System

class FileExt (lang: String) where
  ext: String -- fileExtension

class BuildCode (lang: String) where
  bld: FilePath → IO Unit
class ExeCode   (lang: String) where
  exe:   FilePath → IO String

class BenchCode   (lang: String) where
  -- iterations, time
  exe:   FilePath → IO (Nat × Float)

-- todo: time???

-- to consider warm up (jit) we are practically pressured into doing that in python or at the bare minimum repetitions in python (so through a big array???)


-- import Polara.Codegeneration.IO.All
-- import Polara.Codegeneration.Parse

-- class Codegen (lang: String) where
--   gen : Tm VPar α → String

-- class Eval (lang: String) where
--   eval {α: Ty}: Tm VPar α → IO α.val?

-- instance evalI (lang)[c: Codegen lang](fileExt: String)
--   [b: BuildCode lang][e: ExeCode lang]: Eval lang where
--     eval {α: Ty}(term: Tm VPar α) := do
--       let code := c.gen term
--       let file  ← writeTmpFile fileExt code
--       let _     ← b.bld file
--       let out   ← e.exe file
--       let val  := α.parse out
--       return val

-- abbrev BenchRes := Nat × Float -- iterations, time
-- abbrev Run := {α: Ty} → (term: Tm VPar α) → (name: String) → IO (String × α.val? × Float)
