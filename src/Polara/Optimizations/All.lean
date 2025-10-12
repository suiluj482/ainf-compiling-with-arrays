import Polara.Optimizations.NbE
import Polara.Optimizations.CSE
import Polara.Optimizations.Vectorization
import Polara.Optimizations.CleanEnv
import Polara.Optimizations.Basics
import Polara.Optimizations.Dead
import Polara.Optimizations.Convert.All
import Polara.Optimizations.Analyse.All
---
import Polara.Codegeneration.All

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
  -- (
  --   "ainf",
  --   λ n t => do
  --     let ainf := t.toAINF
  --     let _ ← writeTmpFile s!"{n}.ainf" ainf.toString
  --     return ainf.toTm
  -- ),
  (
    "ainfOptimize",
    λ n t => do
    let s := t.toAINF
    let s := s.cleanEnv
    let _ ← writeTmpFile s!"{n}_cleanEnv.ainf" s.toString
    let s := s.cse
    let _ ← writeTmpFile s!"{n}_cse.ainf" s.toString
    let s := s.vectorize
    let _ ← writeTmpFile s!"{n}_vectorize.ainf" s.toString
    let s := s.dead
    let _ ← writeTmpFile s!"{n}_dead.ainf" s.toString
    let s := s.toTm
    let _ ← writeTmpFile s!"{n}_toTm.ainf" s.toString
    return s.normVPar
  ),
]
