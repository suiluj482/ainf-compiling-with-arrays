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

abbrev Pipeline := {α: Ty} → String → Tm VPar α → IO (Tm VPar α)

def pipelines: List (String × Pipeline) := [
  (
    "noOptimization",
    λ _ t => return t
  ),
  (
    "norm",
    λ _ t => return t.normVPar
  ),
  (
    "ainf",
    λ s t => return t.toAINF.toTm
  ),
  (
    "ainfOptimize",
    λ s t => return t.toAINF
      |>.cleanEnv
      |>.cse
      |>.vectorize
      |>.dead
    |>.toTm
  ),
]
