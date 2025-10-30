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

open PipelineM

abbrev TmPipeline (α: Ty) := PipelineM String String (Term α) (Term α)

private def metaT (name: String)(fullName: String)(t: Term α)(time: Float): IO String := do
  let _ ← writeTmpFile s!"{fullName}/{name}.polara" t.toString
  return s!"{name}: {"{"}
time: {time}
size: {t.size}
ops: {t.numOps}, controlFlow: {t.numControlFlow}
{"}"}"

private def metaA (name: String)(fullName: String)(t: AINF α)(time: Float): IO String := do
  let _ ← writeTmpFile s!"{fullName}/{name}.ainf" t.toString
  return s!"{name}: {"{"}
time: {time}
size: {t.size}
ops: {t.numOps}, controlFlow: {t.numControlFlow}
{"}"}"

def pipelines (α: Ty): List (String × (TmPipeline α)) := [
  ("noOptimization", .nil),
  ("norm", nil
    |>.cons (metaT "norm") Tm.normVPar
  ),
  ("ainf", nil
    |>.cons (metaA "noOp_toAINF") Tm.toAINF
    |>.cons (metaT "noOp_fusion") AINF.fusion
  ),
  ("ainfOptimize", nil
    |>.cons (metaT "norm") Tm.normVPar
    |>.cons (metaA "toAINF") Tm.toAINF
    |>.cons (metaA "cleanEnv") AINF.cleanEnv
    |>.cons (metaA "cse") AINF.cse
    |>.cons (metaA "vectorize") AINF.vectorize
    |>.cons (metaA "dead") AINF.dead
    |>.cons (metaT "fusion") AINF.fusion
  )
]
