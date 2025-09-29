import Polara.Codegeneration.IO.All
import Polara.Codegeneration.Parse

class Codegen (lang: String) where
  gen : Tm VPar α → String
