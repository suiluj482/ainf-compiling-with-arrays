import Polara.Syntax.All
import Polara.Optimizations.Convert.ToAinf
open Std

private abbrev SBnd := ((β: Ty) × Var β × Prim β)

private abbrev UsesMap := HashMap (Sigma Var) (List (Sigma Var × (EnvPart × Env)))
private abbrev UsedMap := HashMap (Sigma Var × EnvPart) (List SBnd)

private def Prim.getOpenedEnvs: Prim α → List (Sigma Var × EnvPart)
| .abs i a => a.var?.map (⟨_,·⟩, .func _ i) |>.toList
| .bld i a => a.var?.map (⟨_,·⟩, .forc _ i) |>.toList
| .ite c a b =>
    (a.var?.map (⟨_,·⟩, .itec c true)).toList
    ++ (b.var?.map (⟨_,·⟩, .itec c false)).toList
| _ => []

private def Bnds.getUsedMap' (usesMap: UsesMap): Bnds → ((List SBnd) × UsedMap)
| [] => ([], .emptyWithCapacity 10)
| (bnd: Bnd) :: bnds =>
    let ⟨v,env,prim⟩ := bnd

    -- mark uses with deeper envs
    let openedEnvs := prim.getOpenedEnvs
    let usesMap := openedEnvs.foldl
      (λ usesMap (v', envPart) =>
        usesMap.alter v' (λ
          | none => [(v,envPart, env)]
          | some uses' => (v,envPart, env) :: uses'
        )
      )
      usesMap

    -- dbg_trace s!"{v.snd}: openedEnvs={openedEnvs} usesMap={usesMap.toList}"

    let uses := usesMap.get? v |>.getD []
    -- filter out uses with shallower envs
    let uses := uses.filter (λ (_,(envPart', env')) => env.isSubsetOf (envPart' :: env'))

    -- mark uses with same depth
    let usesMap := if uses≠[] then -- unnecessary, if no uses
        let neededVars := bnd.vars--.removeAll (openedEnvs.map (·.fst))
        neededVars.foldl
        (λ usesMap v =>
          usesMap.alter v (λ
            | none => uses
            | some uses' => uses'.addSets uses
          )
        )
        usesMap
      else usesMap

    -- recursive call
    let (resBnds, usedMap) := Bnds.getUsedMap' usesMap bnds

    -- write uses into usedMap
    let usedMap := uses.foldl
      (λ usedMap (v',(envPart',_)) => usedMap.alter (v',envPart') (λ
          | none      => some <| [⟨v.fst,v.snd,prim⟩]
          | some defs => some <| defs.concat ⟨v.fst,v.snd,prim⟩
        )
      )
      usedMap

    -- if env≠[], bnd allready in usedMap
    let resBnds := if env==[] then (⟨v.fst,v.snd,prim⟩ :: resBnds) else resBnds

    (resBnds, usedMap)
private def Bnds.getUsedMap (bnds: Bnds) := (Bnds.getUsedMap' (.emptyWithCapacity 10) bnds.reverse).map List.reverse id
def AINF.getUsedMap (a: AINF α) := a.fst.getUsedMap


private abbrev Ren := DHashMap (Sigma VPar) (λ ⟨α,_⟩ => VPar α)
private def Ren.apply: Ren → VPar α → Term α
| r, v => .var (match r.get? ⟨_,v⟩ with
  | some v => v
  | none => panic! s!"Ren.apply no entry for {v} found in {r.toList}"
  )

-- @[reducible]
-- private def Ty.envPart: EnvPart → Ty → Ty
-- | .itec _ _ => id
-- | .forc _ (n:=n) => Ty.array n
-- | .func _ (α:=α) => Ty.arrow α

private abbrev UsedTermMap := DHashMap (Sigma Var × Env) (λ (⟨α,_⟩,_) => Term α)
private partial def assemble (bnds: List SBnd)(env: Env)(usedMap: UsedMap)(usedTermMap: UsedTermMap)(ren: Ren)(c: Ren → Term α): Term α :=
  match bnds with
  | [] => c ren
  | bnd :: bnds =>
      let ⟨α,v,prim⟩ := bnd

      let primTm := match α, prim with
        | _, .abs i a =>
            fun'v i' =>
              let envPart := (.func _ i)
              let ren: Ren := ren.insert ⟨_,(.p i)⟩ i'
              match usedMap.get? (⟨_,v⟩, envPart) with
              | none => Tm.var a
              | some bnds =>
                  assemble
                    bnds env usedMap (.emptyWithCapacity 1) ren
                    (λ ren => ren.apply a)
        | _, .bld i a =>
            for'v i' =>
              let envPart := (.forc _ i)
              let ren: Ren := ren.insert ⟨_,.p i⟩ i'
              match usedMap.get? (⟨_,v⟩, envPart) with
              | none => Tm.var a
              | some bnds =>
                  assemble
                    bnds env usedMap (.emptyWithCapacity 1) ren
                    (λ ren => ren.apply a)
        | _, .ite c a b =>
            if' ren.apply c
              then
                let envPart := (.itec c true)
                match usedMap.get? (⟨_,v⟩, envPart) with
                | none => Tm.var a
                | some bnds =>
                    assemble
                      bnds env usedMap (.emptyWithCapacity 1) ren
                      (λ ren => ren.apply a)
              else
                let envPart := (.itec c false)
                match usedMap.get? (⟨_,v⟩, envPart) with
                | none => Tm.var b
                | some bnds =>
                    assemble
                      bnds env usedMap (.emptyWithCapacity 1) ren
                      (λ ren => ren.apply b)
        | _, .err           => Tm.err
        | _, .var v         => ren.apply v
        | _, .cst0 c        => Tm.cst0 c
        | _, .cst1 c v      => Tm.cst1 c (ren.apply v)
        | _, .cst2 c v1 v2  => Tm.cst2 c (ren.apply v1) (ren.apply v2)

      let'v v' := primTm;
      let ren := ren.insert ⟨_,(.v v)⟩ v'
      assemble
        bnds env usedMap usedTermMap ren c


def AINF.fusion: AINF α → Term α
| (bnds, ret) =>
    let (bnds, usedMap) := Bnds.getUsedMap bnds
    assemble
      bnds
      []
      usedMap
      (.emptyWithCapacity usedMap.size)
      (.emptyWithCapacity bnds.length)
      (λ ren => ren.apply (.v ret))


-- open Ty

-- #eval (tlitf 1).exp.toAINF.fusion
-- #eval (tlitf 1 + tlitf 1 * tlitf 2).toAINF.fusion
-- #eval (let' a:= tlitf 1; fun' x:flt => x+a).toAINF.fusion
-- #eval (for' i:5 => fun' x => if' x <' tlitf 0 then i.i2n.n2f + x else x).toAINF.fusion

-- #eval (fun' x:Ty.flt => x).toAINF.fusion
-- #eval (fun' x:Ty.flt => x).toAINF.getUsedMap.fst
-- #eval (fun' x:Ty.flt => x).toAINF.getUsedMap.snd.toList

-- #eval ((fun' x:Ty.flt => x+x) @@ tlitf 1).toAINF
-- #eval ((fun' x:Ty.flt => x+x) @@ tlitf 1).toAINF.getUsedMap.fst
-- #eval ((fun' x:Ty.flt => x+x) @@ tlitf 1).toAINF.getUsedMap.snd.toList

-- #eval (fun' x:flt => fun' y:flt => x+y).toAINF.fusion
-- #eval (fun' x:flt => fun' y:flt => x+y).toAINF.getUsedMap.fst
-- #eval (fun' x:flt => fun' y:flt => x+y).toAINF.getUsedMap.snd.toList

-- #eval (if' tlitn 0 then tlitf 1 else tlitf 2).toAINF.fusion
-- #eval (if' tlitn 0 then tlitf 1 else tlitf 2).toAINF.getUsedMap.fst
-- #eval (if' tlitn 0 then tlitf 1 else tlitf 2).toAINF.getUsedMap.snd.toList
