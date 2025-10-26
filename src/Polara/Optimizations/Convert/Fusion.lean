import Polara.Syntax.All
import Polara.Optimizations.Convert.ToAinf
open Std

def SBnd := ((β: Ty) × Var β × Prim β)

abbrev UsesMap := HashMap (Sigma Var) (List (Sigma Var × Env))
abbrev UsedMap := HashMap (Sigma Var) (List Bnd)

def Bnds.getUsedMap' (usesMap: UsesMap): Bnds → ((List SBnd) × UsedMap)
| [] => ([], .emptyWithCapacity 10)
| (bnd: Bnd) :: bnds =>
    let ⟨v,env,prim⟩ := bnd

    -- mark uses with deeper envs
    let openedEnvs: List (Sigma Var × EnvPart) := match v.fst, prim with
      | _, .abs i a => a.var?.map (⟨_,·⟩, .func _ i) |>.toList
      | _, .bld i a => a.var?.map (⟨_,·⟩, .forc _ i) |>.toList
      | _, .ite c a b =>
          (a.var?.map (⟨_,·⟩, .itec c true)).toList
          ++ (b.var?.map (⟨_,·⟩, .itec c false)).toList
      | _, _ => []
    let usesMap := openedEnvs.foldl
      (λ usesMap (v', envPart) =>
        usesMap.alter v' (λ
          | none => [(v,envPart :: env)]
          | some uses' => (v,envPart :: env) :: uses'
        )
      )
      usesMap

    -- dbg_trace s!"{v.snd}: openedEnvs={openedEnvs} usesMap={usesMap.toList}"

    match usesMap.get? v with
    | none =>
        -- dbg_trace s!"{v.snd}: no uses in usesMap={usesMap.toList}"
        Bnds.getUsedMap' usesMap bnds |>.map
          -- if env≠[], bnd is in usedMap -> not needed in resBnds
          (λ resBnds => if env==[] then (⟨v.fst,v.snd,prim⟩ :: resBnds) else resBnds)
          id
    | some uses =>

        -- filter out uses with shallower envs
        let uses := uses.filter (λ (_,env') => env==env')
        -- mark uses with same depth
        let neededVars := bnd.vars.removeAll (openedEnvs.map (·.fst))
        let usesMap := neededVars.foldl
          (λ usesMap v =>
            usesMap.alter v (λ
              | none => uses
              | some uses' => uses'.addSets uses
            )
          )
          usesMap

        -- recursive call
        let (resBnds, usedMap) := Bnds.getUsedMap' usesMap bnds

        -- write uses into usedMap
        let usedMap := uses.foldl
          (λ usedMap (v,_) => usedMap.alter v (λ
              | none => [bnd]
              | some defs => defs.concat bnd
            )
          )
          usedMap

        (resBnds, usedMap)
def Bnds.getUsedMap (bnds: Bnds) := (Bnds.getUsedMap' (.emptyWithCapacity 10) bnds.reverse).map List.reverse id
def AINF.getUsedMap (a: AINF α) := a.fst.getUsedMap




open Ty

#eval (fun' x:Ty.flt => x).toAINF
#eval (fun' x:Ty.flt => x).toAINF.getUsedMap.fst
#eval (fun' x:Ty.flt => x).toAINF.getUsedMap.snd.toList

#eval ((fun' x:Ty.flt => x+x) @@ tlitf 1).toAINF
#eval ((fun' x:Ty.flt => x+x) @@ tlitf 1).toAINF.getUsedMap.fst
#eval ((fun' x:Ty.flt => x+x) @@ tlitf 1).toAINF.getUsedMap.snd.toList

#eval (if' tlitn 0 then tlitf 1 else tlitf 2).toAINF
#eval (if' tlitn 0 then tlitf 1 else tlitf 2).toAINF.getUsedMap.fst
#eval (if' tlitn 0 then tlitf 1 else tlitf 2).toAINF.getUsedMap.snd.toList















-- def SBnd := ((β: Ty) × Var β × Prim β)

-- @[reducible]
-- def Ty.envPart: EnvPart → Ty → Ty
-- | .itec _ _ => id
-- | .forc _ (n:=n) => Ty.array n
-- | .func _ (α:=α) => Ty.arrow α

-- abbrev EnvPart.EscapingVar (e: EnvPart) := (α: Ty) × VPar (α.envPart e) × VPar α

-- def BndTree := List (Tree ((e: EnvPart) × e.EscapingVar) SBnd)
-- def AINFTree (α: Ty) := BndTree × VPar α

-- def fuse (bnds: BndsH)(env: Env)(var: Var α)(done: BndTree): Term α :=
--   let (placeable, rest) := bnds.partition
--     (λ v (env, prim) =>
--       let reqVars := env.vars ++ prim.vars
--       reqVars.filter bnds.contains |>.isEmpty
--     )
--   match startNodes.isEmpty, m'.isEmpty with
--   | true, true => done
--   | true, false => panic! "topologicalSort error no dag"
--   | _, _ =>
--     sorry


--   sorry

















-- import Polara.Optimizations.Convert.ToTm

------
-- def SBnd := ((β: Ty) × Var β × Prim β)

-- @[reducible]
-- def Ty.envPart: EnvPart → Ty → Ty
-- | .itec _ _ => id
-- | .forc _ (n:=n) => Ty.array n
-- | .func _ (α:=α) => Ty.arrow α

-- abbrev EnvPart.EscapingVar (e: EnvPart) := (α: Ty) × VPar (α.envPart e) × VPar α

-- def BndTree := List (Tree ((e: EnvPart) × List e.EscapingVar) SBnd)
-- def AINFTree (α: Ty) := BndTree × VPar α

-- partial def BndTree.toString: BndTree → String
-- | bndTree => bndTree.map (λ node =>
--     match node with
--     | Tree.leaf ⟨_,v,prim⟩ => s!"let {v} := {prim}\n"
--     | Tree.node ⟨envPart, escVars⟩ tree' =>
--         let (tVars, sVars) := escVars
--           |>.map (λ (⟨_,y,x⟩: envPart.EscapingVar) => (s!"{y}",s!"{x}"))
--           |>.unzip
--         let treeS := BndTree.toString tree' |>.indent
--         s!"let {tVars} := {envPart}\n{treeS}{sVars}"
--   ) |> Print.foldLines

-- def AINFTree.toString: AINFTree α → String
-- | (tree, v) => s!"{tree.toString}{v}"
-- instance: ToString (AINFTree α) := ⟨AINFTree.toString⟩

-- open Std
-- abbrev Ren := ListMap VPar VPar
-- def Ren.apply: Ren → VPar α → Term α
-- | r, v => Tm.var (r.lookup! v)

-- def Prim.toTm (ren: Ren): Prim α → Term α
-- | err           => Tm.err
-- | var v         => ren.apply v
-- | cst0 c        => Tm.cst0 c
-- | cst1 c v      => Tm.cst1 c (ren.apply v)
-- | cst2 c v1 v2  => Tm.cst2 c (ren.apply v1) (ren.apply v2)
-- | ite cond a b  => Tm.ite (ren.apply cond) (ren.apply a) (ren.apply b)
-- | abs _ _
-- | bld _ _ => panic! "Fusion Prim.toTm"


-- def BndTree.toTm (e: Env)(r: Ren): BndTree → (Term α → Term α × Ren)
-- | [] => (λ t => (t, r))
-- | node :: bndTree' => match node with
--   | .leaf ⟨_,v,prim⟩ =>
--       λ t => (let'v v' := prim.toTm r; t, ⟨_,.v v,.v v'⟩ :: r)
--   | .node ⟨envPart, escVars⟩ tree' => sorry

-- def AINFTree.toTm: AINFTree α → Term α
-- | (tree, v) => Tm.var v





-- abbrev BndPrim := @Sigma (Sigma Var) (λ ⟨α,_⟩ => Prim α)
-- abbrev BndTree := LTree EnvPart BndPrim
-- def AINFTree (α: Ty) := BndTree × VPar α



-- Operation deckt eine Env?
-- Analyse auf variablen, die nur innerhalb der env verwendet werden

-- todo optimize by allowing reorderings, diffrent order to prevent all the accesss to last element maybe also better for reordering
-- scope of binding isn't limited to subnodes, yet?
-- def BndTree.addBnd(tree: BndTree)(envBnd: EnvBnd): BndTree :=
--   (
--     match List.getLast? tree, envBnd with
--     | some (Tree.node envPart' tree'), (envPart :: envList, bnd) =>
--         if envPart == envPart' then
--           -- envBnd shares same first envPart with last child => can be added to it
--           some (tree.dropLast |>.concat (Tree.node envPart' (BndTree.addBnd tree' (envList, bnd))))
--         else none
--     | _, _ => none
--   ).getD (tree.concat (envBnd.fst.foldr (λ envPart acc => Tree.node envPart [acc]) (Tree.leaf envBnd.snd)))
-- termination_by envBnd.fst

-- def AINF.toTree (a: AINF α): AINFTree α :=
--   a.toList.map (λ l => l.foldl (λ acc envBnd => acc.addBnd envBnd) []) id


-- whats official semantic of envParts at the order at which they "need" to be destructed
--   probably none, that makes fusion harder

-- conservative Annahme nur terme die nur in env gebraucht werden fusen
-- eventuell mehrere exits als tuple rausschleusen, wirklich effizienter?

-- womit kommt das target klar?, ist unser Term eine einschränkung mit nur einem ergebnis eines fors?

-- open Ty
-- def x0: Var nat := .mk 0
-- def x1: Var flt := .mk 1
-- def x2: Var flt := .mk 2
-- def x3: Var flt := .mk 3
-- def x4: Var flt := .mk 4
-- def x10: Var (flt.array 10) := .mk 10
-- def x11: Var (flt.array 10) := .mk 11

-- def i0: Par (idx 10) := .mk 0
-- def i1: Par (idx 10) := .mk 0
-- #eval ((
--   [
--     let'' [] in x3 := .cst0 (.litf 0.1),
--     let'' [.forc 10 i0, .forc 10 i1] in x0 := .cst1 .i2n (.p i0),
--     let'' [.forc 10 i0, .forc 10 i1] in x1 := .cst1 .n2f (.v x0),
--     -- array array ...
--     let'' [.forc 10 i1] in x10 := for'' i0:10, (.v x1),
--     let'' [.forc 10 i0] in x10 := for'' i1:10, (.v x1),

--     let'' [] in x4 := .cst0 (.litf 0.2),

--     let'' [.forc 10 i0] in x2 := .cst2 (.arithOp .add) (.v x1) (.v x3),

--     -- here two exits
--     let'' [] in x10 := for'' i0:10, (.v x1),
--     let'' [] in x11 := for'' i0:10, (.v x2),
--   ],
--   (.v x1)
-- ): AINF flt)

-- #eval (for' i: idx ⟨10, => i.i2n.n2f + 2)
