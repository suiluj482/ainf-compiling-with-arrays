import Polara.Syntax.Index
import Polara.Optimizations.ToAinf
import Polara.Optimizations.AutomaticDifferentation
import Std

-- transpose linear
-- transpose

@[reducible]
def Ty.tl: Ty → Ty :=
  Ty.map (λ
    | .lin => ref lin
    | α => α
  )

def Const0.tl: Const0 α → Term α.tl
| .litl l => .cst0 <| .mkRef
| .litn n => .cst0 <| .litn n
| .litf f => .cst0 <| .litf f
| .liti i => .cst0 <| .liti i
| .litu => .cst0 <| .litu
| .mkRef => panic! "Const0.tl doesn't support references"

def Const1.tl (c: Const1 α β) (a: Term α.tl): Term β.tl :=
  match c with
  | .exp => .cst1 .exp a
  | .sqrt => .cst1 .sqrt a
  | .log => .cst1 .log a
  | .normCdf => .cst1 .normCdf a
  | .fst => .cst1 .fst a
  | .snd => .cst1 .snd a
  | .sumf => .cst1 .sumf a
  | .suml => (let' rx :=& x;
      (
        for' i => a[[i]] *:= x
      ).dumpFor rx
    )
  | .i2n => .cst1 .i2n a
  | .n2f => .cst1 .n2f a
  | .refGet => panic! "Const1.tl doesn't support references"

def linOpTl [t: BiArraysC BiLin α β γ](op: AddOp)
  (a: Tm Γ α.tl)(b: Tm Γ β.tl): Tm Γ γ.tl :=
  match t.t with
  | .array n t' =>
      have: BiArraysC BiLin _ _ _ := ⟨t'⟩
      for' i => (linOpTl op a[[i]] b[[i]])
  | .base t' => match t' with
    | .lins => match op with
      | .add => (let' rx :=& x;
        a *:= x;
        b *:= x;
        rx
      )
      | .sub => (let' rx :=& x;
        a *:= x;
        b *:= tlitl 0 - x;
        rx
      )
def linScaleTl [t: BiArrayC BiLF α β γ](op: MulOp)
  (a: Tm Γ α.tl)(b: Tm Γ β.tl): Tm Γ γ.tl :=
  let go {α' β' γ'}(t: BiLF α' β' γ')(a: Tm Γ α'.tl)(b: Tm Γ β'.tl): Tm Γ γ'.tl :=
    match t with
    | .lf => match op with
      | .mul => (let' rx :=& x;
        a *:= x * b;
        rx
      )
      | .div => (let' rx :=& x;
        a *:= x / b;
        rx
      )
  match t.t with
  | .array n t' => for' i => go t' a[[i]] b[[i]]
  | .base t' => go t' a b

def Const2.tl (c: Const2 α β γ)(a: Term α.tl)(b: Term β.tl): Term γ.tl :=
  match c with
  | .arithOp (type:=t) op =>
    have: BiArraysC BiArith α.tl β.tl γ.tl := ⟨
      let rec go {α β γ: Ty}: BiArrays BiArith α β γ → BiArrays BiArith α.tl β.tl γ.tl
      | .array n t' => .array n (go t')
      | .base t' => .base (match t' with | .nats => .nats | .flts => .flts)
      go t.t⟩
    .cst2 (.arithOp op) a b
  | .addi => .cst2 .addi a b
  | .maxf => .cst2 .maxf a b
  | .lt => .cst2 .lt a b
  | .get => .cst2 .get a b
  | .tup => .cst2 .tup a b
  | .app => .cst2 .app a b
  | .linOp (type:=t) op => linOpTl op a b
  | .linScale (type:=t) op => linScaleTl op a b
  | .refSet => panic! "Const2.tl doesn't support references"

-- could be stopped from going deeper as soon as there is no lin in type
def Tm.tl': Term α → Term α.tl
| .err => .err
| .var v => .var v.changeType
| .bnd t f => .bnd t.tl' (λ v => f v.changeType |>.tl')
| .abs f => .abs (λ v => f v.changeType |>.tl')
| .bld f => .bld (λ i => (f i).tl')
| .ite cond a b => .ite cond a.tl' b.tl'
| .cst0 cst => cst.tl
| .cst1 cst a => cst.tl a.tl'
| .cst2 cst a b => cst.tl a.tl' b.tl'

def Tm.tl (t: Term α): Term α.tl :=
  t.tl'


@[reducible]
def Ty.liftTup: Ty → Ty
| array n (α ×× β) => (array n α) ×× (array n β)
| α ~> (β ×× γ) => (α ~> β) ×× (α ~> γ) -- to AINF funktionen zerlegen

| _ => nat

-- lieber ainf erweiteren als unzipping

@[reducible]
def Ty.combineFuncs: Ty → Ty
| α ~> (β ~> γ) => (α ×× β) ~> γ.combineFuncs
| α => α

-- remove?
-- (flt × lin.ref)                    uz= (flt, lin.ref)
-- flt × lin.ref ~> (flt × lin.ref)   uz= (flt ~> flt, lin.ref ~> lin.ref)
-- lin.ref ~> lin.ref                 uz= (none, lin.ref ~> lin.ref)
-- flt ~> flt                         uz= (flt ~> flt, none)

-- replace with unit?
-- (flt × lin.ref)                    uz= (flt × unit, lin.ref)
-- flt × lin.ref ~> (flt × lin.ref)   uz= (flt × unit ~> flt × unit, lin.ref ~> lin.ref)
-- lin.ref ~> lin.ref                 uz= (unit ~> unit, lin.ref ~> lin.ref)
-- flt ~> flt                         uz= (flt ~> flt, none?)
@[reducible]
def Ty.unzipRefs (α: Ty): (Option Ty) × (Option Ty) :=
  match α with
  | .ref α => (none, α.ref)
  | unit => (unit, none)
  | .nat => (nat, none)
  | .flt => (flt, none)
  | .lin => (lin, none)
  | .idx n => (idx n, none)
  | α ×× β =>
    (α.unzipRefs).zip (β.unzipRefs)
    |>.mapBoth (λ (γ, rγ) => γ.merge (·××·) rγ)
  | .array n α => α.unzipRefs.mapBoth (·.map (.array n ·))
  | α ~> β =>
    β.unzipRefs.mapBoth (·.map (α ~> ·))

open Ty in
#eval ((flt ×× (ref lin)) ~> (flt ×× (ref lin))).unzipRefs
open Ty in
#eval (flt ~> (flt ×× (flt ~> flt))).aD.tl.unzipRefs

-- @[reducible] -- ?????
-- def AINF.unzipRefsType (α: Ty): Type :=
--   let (α, β) := α.unzipRefs
--   (Bnds × (α.map (AINF ·)).getD Unit) × (Bnds × (β.map (AINF ·)).getD Unit)
-- def AINF.unzipRefs (a: AINF α): AINF.unzipRefsType α :=
--   sorry

@[reducible]
def Ty.containsRef (t: Ty): Bool :=
  t.contains (λ α => match α with
    | .ref _ => true
    | _ => false)

theorem Ty.unzipRefs_containsRef_false {α: Ty}: α.containsRef=false → α.unzipRefs = (some α, none) := by
  intro h
  match α with
  | .ref _ => contradiction
  | .unit | .nat | .flt | .lin | .idx n => rfl
  | α ×× β =>
    rw[Ty.unzipRefs,
      Ty.unzipRefs_containsRef_false (by simp[h, Ty.contains_product_a α β]),
      Ty.unzipRefs_containsRef_false (by simp[h, Ty.contains_product_b α β])
    ]
    rfl
  | .array n α =>
    rw[Ty.unzipRefs,
      Ty.unzipRefs_containsRef_false (by simp[h, Ty.contains_array n α])
    ]
    rfl
  | α ~> β =>
    rw[Ty.unzipRefs,
      -- Ty.unzipRefs_containsRef_false (by simp[h, Ty.contains_arrow_a α β]),
      Ty.unzipRefs_containsRef_false (by simp[h, Ty.contains_arrow_b α β])
    ]
    rfl

abbrev Ty.unzipRefsT (α: Ty)(f: Ty → Type): Type :=
  -- (
  --   (if h: α.unzipRefs.fst.isSome = true then
  --     f (α.unzipRefs.fst.get h)
  --   else Unit) ×
  --   (if h: α.unzipRefs.snd.isSome = true then
  --     f (α.unzipRefs.snd.get h)
  --   else Unit)
  -- )
  -- let (nα, rα) := α.unzipRefs
  -- (
  --   (if h: nα.isSome = true then
  --     let nα' := nα.get h
  --     f nα'
  --   else Unit) ×
  --   (if h: rα.isSome = true then
  --     let rα' := rα.get h
  --     f rα'
  --   else Unit)
  -- )
  -- ((α.unzipRefs.fst.map f).getD Unit) × ((α.unzipRefs.snd.map f).getD Unit)
  let (nα, rα) := α.unzipRefs
  ((nα.map f).getD Unit) × ((rα.map f).getD Unit)

def Prim.unzipRefs (prim: Prim α): α.unzipRefsT (Prim ·) :=
  match prim with
  | .ref f => ((), .ref f)
  | .var (α:=α) v =>
    -- let (nα, rα) := α.unzipRefs
    let nα := α.unzipRefs.fst
    let rα := α.unzipRefs.snd
    (
      (if h: nα.isSome = true then
        let nα' := nα.get h
        -- have t: Prim nα' =
        --   if h : α.unzipRefs.fst.isSome = true then
        --     let nα' := α.unzipRefs.fst.get h;
        --     (fun x => Prim x) nα'
        --   else Unit
        --   := sorry
        have t: Prim nα' = (Option.map (fun x => Prim x) α.unzipRefs.fst).getD Unit := by
          dsimp
          sorry
        t▸(Prim.var (v.changeType (β:=nα')))
      else
        -- have t: Unit =
        --   if h : α.unzipRefs.fst.isSome = true then
        --     let nα' := α.unzipRefs.fst.get h;
        --     (fun x => Prim x) nα'
        --   else Unit
        --   := sorry
        have t: Unit = (Option.map (fun x => Prim x) α.unzipRefs.fst).getD Unit := sorry
        t▸()),
      (if h: rα.isSome = true then
        let rα' := rα.get h
        have t: Prim rα' =
          if h : α.unzipRefs.snd.isSome = true then
            let rα' := α.unzipRefs.snd.get h;
            (fun x => Prim x) rα'
          else Unit
          := sorry
        t▸(Prim.var (v.changeType (β:=rα')))
      else
        have t: Unit =
          if h : α.unzipRefs.snd.isSome = true then
            let rα' := α.unzipRefs.snd.get h;
            (fun x => Prim x) rα'
          else Unit
          := sorry
        t▸())
    )
    -- (
    --   α.unzipRefs.fst.map (fun nα' => Prim.var (v.changeType (β:=nα'))) |>.getD (),
    --   rα.map (fun rα' => Prim.var (v.changeType (β:=rα'))) |>.getD ()
    -- )
  | _ => sorry

def Prim.unzipRefsN(prim: Prim α)(ok: (Ty.unzipRefs α).fst.isSome = true): Prim ((Ty.unzipRefs α).fst.get ok) :=
  let α' := ((Ty.unzipRefs α).fst.get ok)
  match α, prim with
  | _, .var v => .var (v.changeType (β:=α'))
  | _, .err => .err
  | _, .cst0 c => sorry
  | _, .cst1 c a => sorry
  | _, .cst2 c a b => sorry
  | _, .abs x y => sorry
  | _, .ite c a b => sorry
  | _, .bld i x => sorry
  | _, .bndRef xr x => sorry

theorem Option.map_some_true(h: a = some b): a.map f = some (f b) := by
  rw[h]
  rfl

-- Option.map_congr, Option.map_dif, Option.map_some, Option.map_eq_some_iff
-- unfold_let

-- assume α doesn't contains ref
def AINF.unzipRefs (a: AINF α)(ok: α.containsRef = false): AINF α × Bnds :=
  have: α.unzipRefs = (some α, none) := Ty.unzipRefs_containsRef_false ok
  match a with
  | (bnds, ret) =>
    let bnds': List (Option Bnd × Option Bnd) := bnds.map (λ ⟨⟨α, v⟩, (env, prim)⟩ =>
      -- let (nα, rα) := α.unzipRefs
      let nα := α.unzipRefs.fst
      have let_nα: α.unzipRefs.fst = nα := by dsimp
      let rα := α.unzipRefs.snd
      let (nprim, rprim) := prim.unzipRefs
      (
        if h: nα.isSome = true then
          let nα' := nα.get h
          have h': nα = some nα' := by
            simp[nα']
          have t: (Option.map (fun x => Prim x) α.unzipRefs.fst).getD Unit = Prim nα' := by
            simp[h', let_nα, Option.map_some_true h']
          some ⟨⟨nα', v.changeType⟩, env, t▸nprim⟩ -- term required?
        else none,
        if h: rα.isSome then
          let rα' := rα.get h
          have h': α.unzipRefs.snd = rα := by sorry
          have t: (Option.map (fun x => Prim x) α.unzipRefs.snd).getD Unit = Prim rα' := sorry
          some ⟨⟨rα', v.changeType⟩, env, t▸rprim⟩ -- term required?
        else none,
      )
    )
    let (bnds, refBnds) := bnds'.unzip
    ((bnds.filterMap id, ret), refBnds.filterMap id)

-- more General
-- def AINF.unzipRefs (a: AINF α):
--   (Bnds × (α.unzipRefs.fst.map (VPar ·)).getD Unit)
--   × (Bnds × (α.unzipRefs.fst.map (VPar ·)).getD Unit) :=
--   match a with
--   | (bnds, ret) =>
--     let bnds': List (Option Bnd × Option Bnd) := bnds.map (λ ⟨⟨α, v⟩, (env, prim)⟩ =>
--       (none, none)
--     )
--     let (bnds, refBnds) := bnds'.unzip
--     ((bnds.filterMap id, ret.changeType), refBnds.filterMap ret.changeType)


namespace Test
  open Ty

  def simplest: Term (flt) := tlitf 1

  #eval simplest.aD
  #eval simplest.aD.toAINF

  #eval simplest.aD.tl
  #eval simplest.aD.tl.toAINF

  def simple: Term (flt ~> flt) :=
    fun' x => x

  #eval simple.aD
  #eval simple.aD.toAINF

  #eval simple.aD.tl
  #eval simple.aD.tl.toAINF

  -- #eval ((flt ×× lin) ×× array n (flt ×× lin))

  def simpleADTLBound: Term (flt ×× lin) :=
    -- how would you capture an array of refs without initializing n refs???
    let' xr :=& x;
      let r := (simple.aD.tl
        @@ ((tlitf 1),, (Tm.var xr))
      );
      r.snd *:= (tlitl 1);
      (r.fst,, (Tm.var x))
    -- let' xr :=& x;
    --   let (res, tlitl 1) := (simple.aD.tl
    --     @@ ((tlitf 1),, (Tm.var xr))
    --   );
    --   (res,, (Tm.var x))

  #eval simpleADTLBound

  def add: Term ((flt ×× flt) ~> flt) :=
    fun' t => t.fst + t.snd

  #eval add.aD
  #eval add.aD.toAINF

  #eval add.aD.tl
  #eval add.aD.tl.toAINF

  def add2: Term (flt ~> flt) :=
    fun' x => x + x

  #eval add2.aD
  #eval add2.aD.tl -- fuck (snd i0) gets assigned 2 times
  -- never can also happen

  def add3: Term (flt ~> flt) :=
    fun' x => x + tlitf 1

  def add4: Term (flt ~> flt ~> flt) :=
    fun' x => fun' y => x + y

end Test



-- def AINF.removeInnerRefs (t: Term α): Term α :=
--   sorry

-- -- def mul_transpose_rule(cts, x, y):
-- --   z_bar, = cts
-- --   assert (type(x) is UndefPrimal) ^ (type(y) is UndefPrimal)
-- --   return [mul(z_bar, y), None] if type(x) is UndefPrimal else [None, mul(x, z_bar)]
-- -- transpose_rules[mul_p] = mul_transpose_rule

-- private def helper (env: List EnvPart)(v: VPar α)(t: Tm VPar α): VParM Bnds :=
--   match v with
--   | .v v => t.toAINFMEV env v
--   | .p _ => panic! ""

-- def linOpT [t: BiArraysC BiLin α β γ](op: AddOp)
--   (a: VPar α)(b: VPar β)(c: VPar γ): VParM Bnds :=
--   match t.t with
--   | .array n t' =>
--       have: BiArraysC BiLin _ _ _ := ⟨t'⟩
--       -- for' i => (linOpAD op a[[i]] b[[i]])
--       pure [] -- todo
--   | .base t' => match t' with
--     | .lins => match op with
--         | .add => do return [
--             ←helper [] a (.var c),
--             ←helper [] b (.var c)
--           ] -- (c, c)
--         | .sub => do return
--             ←helper [] a (.var c) |>.append
--             ←helper [] b (.var c)
--           ) -- (c, c)

-- def linScaleT [t: BiArrayC BiLF α β γ](op: MulOp)
--   (a: VPar α)(b: VPar β)(c: VPar γ): VParM Bnds :=
--   let go {α' β' γ'}[t: BiLFC α' β' γ'](a: VPar α')(b: VPar β')(c: VPar γ'): VParM Bnds :=
--     match t.t with --- a lin b flt c lin
--     | .lf => match op with
--         | .mul => helper [] a ((.var c)*(.var b))
--         | .div => helper [] a ((.var c)/(.var b))

--   match t.t with
--   | .array n t' =>
--       have: BiLFC _ _ _ := ⟨t'⟩
--       pure []
--       -- for' i => (go a[[i]] b[[i]])
--   | .base t' =>
--       have: BiLFC _ _ _ := ⟨t'⟩
--       go a b c


-- def Const2.transpose (cst2: Const2 α β γ)(a: VPar α)(b: VPar β)(c: VPar γ): VParM Bnds :=
-- match cst2 with
-- | linOp op => linOpT op a b c
-- | linScale op => linScaleT op a b c
-- | _ => panic "Shouldn't return lin"

-- -- erst lineare und nicht-linear trennen, nicht nichtlineare nochmal trennen?

-- -- lineare <-> nicht lineare Variable? argumente oder rückgabewert
-- def Bnd.transpose (b: Bnd): VParM Bnds :=
--   match b with
--   | ⟨⟨α,v⟩, env, prim ⟩ =>
--       if t: α = Ty.lin then  -- panic bei mult weil lin linear
--         match prim with
--         | .err => sorry
--         | .cst0 cst => pure []
--         | .cst1 cst a => sorry
--         | .cst2 cst a b => cst.transpose a b (.v v)
--         | .var x => helper env x (.var (.v v))
--         | .abs x v => sorry
--         | .ite cond a b => helper env a (.ite (.var cond) (.var (.v v)) (t▸tlitl 0))
--         | .bld x v => sorry
--       else pure [b]

-- def AINF.transpose' : AINF α → VParM (AINF α.tl)
--   | (bnds, ret) => do
--     let ll ← bnds.mapM Bnd.transpose
--     let l := ll.flatMap id
--     let gl := DListMap.groupByKey l
--     let sl: List Bnds ← gl.mapM (λ ⟨⟨α,v⟩,l⟩ => do
--       let (env,_) := l.head!
--       -- give new vars (all should have same type)
--       let newVars: List (Var α) ← l.mapM (λ _ =>
--         return (←VParM.var) α
--       )
--       let bnds: Bnds := newVars.zipWith (λ v (env, prim) => ⟨⟨_,v⟩,env,prim⟩) l
--       -- add these up t original var
--       let tms := newVars.map (λ v => (Tm.var v))
--       let sumBnds: Bnds ← if ne' : tms.isEmpty=false then
--           have ne: tms≠[] := by rw[←List.isEmpty_eq_false_iff]; exact ne'
--           let sum: Tm VPar α := tms.fold1 (λ a b => a+b) ne -- todo figure out summing of weird types
--           sum.toAINFMEV env v
--         else panic! "at least one ele with key must exist"

--       return bnds.append sumBnds
--     )
--     let bnds' := sl.flatMap id
--     return (bnds', ret) -- ret?, type?

-- def Ainf.transpose (a: AINF α): AINF α.tl :=
--   a.transpose'.freshAINFVars a
