import Polara.Optimizations.NbE
import Polara.Optimizations.CSE
import Polara.Optimizations.Unzip
import Polara.Optimizations.Defunc
import Polara.Optimizations.Vectorization
import Polara.Optimizations.CleanEnv
import Polara.Optimizations.Basics
import Polara.Optimizations.Dead
import Polara.Optimizations.Convert.All
import Polara.Optimizations.Analyse.All
---


abbrev Pipeline := {α: Ty} → Tm VPar α → Tm VPar α

def pipelines: List (String × Pipeline) := [
  (
    "noOptimization",
    id
  ),
  (
    "norm",
    (·.normVPar)
  ),
  (
    "ainf",
    (·.toAINF.toTm)
  ),
  (
    "ainfOptimize",
    (·.toAINF
      |>.cleanEnv
      |>.cse
      |>.vectorize
      |>.dead
    |>.toTm)
  ),
]
