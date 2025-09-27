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
