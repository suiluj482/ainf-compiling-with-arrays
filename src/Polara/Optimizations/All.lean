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

abbrev TreeS := Tree String String
abbrev TmPipeline (α: Ty) := PipelineM String TreeS (Term α) (Term α)

private def metaT (name: String)(fullName: String)(t: Term α)(time: Float): IO TreeS := do
  let _ ← writeTmpFile s!"{fullName}/{name}.polara" t.toString
  return (Tree.node name [
    Tree.leaf s!"\"time\": {time}",
    Tree.leaf s!"\"size\": {t.size}",
    Tree.leaf s!"\"ops\": {t.numOps}",
    Tree.leaf s!"\"controlFlow\": {t.numControlFlow}",
  ]).flatJsonInline

private def metaA (name: String)(fullName: String)(t: AINF α)(time: Float): IO TreeS := do
  let _ ← writeTmpFile s!"{fullName}/{name}.ainf" t.toString
  return (Tree.node name [
    Tree.leaf s!"\"time\": {time}",
    Tree.leaf s!"\"size\": {t.size}",
    Tree.leaf s!"\"ops\": {t.numOps}",
    Tree.leaf s!"\"controlFlow\": {t.numControlFlow}",
  ]).flatJsonInline

def pipelines (α: Ty): List (String × (TmPipeline α)) := [
  ("noOptimization", .nil),
  ("norm", nil
    |>.cons (metaT "norm") Tm.normVPar
  ),
  ("ainf", nil
    |>.cons (metaA "toAINF") Tm.toAINF
    |>.cons (metaT "fusion") AINF.fusion
  ),
  ("ainfNormNoFusion", nil
    |>.cons (metaT "norm") Tm.normVPar
    |>.cons (metaA "toAINF") Tm.toAINF
    |>.cons (metaT "toTm") AINF.toTm
  ),
  ("ainfNorm", nil
    |>.cons (metaT "norm") Tm.normVPar
    |>.cons (metaA "toAINF") Tm.toAINF
    |>.cons (metaT "fusion") AINF.fusion
  ),
  ("ainfOptimizeNoVect", nil
    |>.cons (metaT "norm") Tm.normVPar
    |>.cons (metaA "toAINF") Tm.toAINF
    |>.cons (metaA "cleanEnv") AINF.cleanEnv
    |>.cons (metaA "cse") AINF.cse
    |>.cons (metaA "dead") AINF.dead
    |>.cons (metaT "fusion") AINF.fusion
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
