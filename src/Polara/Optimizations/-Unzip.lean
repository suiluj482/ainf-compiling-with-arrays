import Polara.Optimizations.Basics

@[reducible]
def Ty.isTuple: Ty → Bool := (λ | _ ×× _ => true | _ => false)
@[reducible]
def Ty.containsTuple: Ty → Bool := (Ty.contains · Ty.isTuple)


@[reducible]
def Ty.tupleMap (f: Ty → Ty): Ty → Ty
| α ×× β => α.tupleMap f ×× β.tupleMap f
| α => f α

theorem Ty.tupleMap_noTuple {α: Ty}(h: α.containsTuple = false): α.tupleMap f = f α := by
  match α with
  | _ ×× _ => contradiction
  | α => sorry

def Tm.tupleMap (f: Ty → Ty)(g: {α': Ty} → Tm Γ α' → Tm Γ (f α'))
  (x: Tm Γ α): Tm Γ (α.tupleMap f) :=
  match h: α with
  | α ×× β => (x.fst.tupleMap f g,, x.snd.tupleMap f g)
  | α => -- all cases?, if then else
    have t: Ty.tupleMap f α = f α := by subst h; unfold Ty.tupleMap; sorry
    t▸(g x)

def Tm.tupleDeMap (f: Ty → Ty)(g: {α': Ty} → Tm Γ (f α') → Tm Γ α')
  (x: Tm Γ (α.tupleMap f)): Tm Γ α :=
  match α with
  | α ×× β => (x.fst.tupleDeMap f g,, x.snd.tupleDeMap f g)
  | α =>
    have t: Ty.tupleMap f α = f α := by sorry
    g (t▸x)

@[reducible]
def Ty.unzip' (n: Nat): Ty → Ty := Ty.tupleMap (λ α => Ty.array n α)

-- @[reducible]
-- def Ty.unzip' (n: Nat): Ty → Ty
-- | α ×× β => α.unzip' n ×× β.unzip' n
-- | α => array n α

@[reducible]
def Ty.unzip: Ty → Ty
| .nat      => .nat
| .idx n    => .idx n
| flt       => .flt
| lin       => .lin
| α ~> β    => α.unzip ~> β.unzip
| α ×× β    => α.unzip ×× β.unzip
| ref α     => .ref α.unzip
| unit      => .unit
| array n α =>
  α.unzip.unzip' n

-- #eval (Ty.array 10 (Ty.flt ×× Ty.flt)).unzip
-- #eval (Ty.array 10 (Ty.flt ×× Ty.flt ×× Ty.flt)).unzip
-- #eval (Ty.array 10 (Ty.array 10 (Ty.flt ×× Ty.flt))).unzip
-- #eval (Ty.array 10 (Ty.array 10 (Ty.flt ×× Ty.flt ×× Ty.flt))).unzip

-- def Tm.tupleZipWith {α β γ: Ty}(f: Ty → Ty)(g: {α' β' γ': Ty} → Tm Γ α' → Tm Γ β' → Tm Γ γ')
--   (a: Tm Γ (α.tupleMap f))(b: Tm Γ (β.tupleMap f)): Tm Γ (γ.tupleMap f) :=
--   match α with asdfsad
--   | α ×× β => (Tm.tupleZipWith f g a.fst b.fst,, Tm.tupleZipWith f g a.snd b.snd)
--   | α =>
--     have t: Ty.tupleMap f α = f α := by sorry
--     g (t▸a) (t▸b)

-- def ArithOp.unzip (t: BiArith α β γ)(op: ArithOp)
--   (a: Tm Γ α.unzip)(b: Tm Γ β.unzip): Tm Γ γ.unzip :=
--   match t with
--   | .nats => Tm.cst2 (.arithOp op) a b
--   | .flts => Tm.cst2 (.arithOp op) a b
-- def linOpDf (t: BiLin α β γ)(op: AddOp)
--   (a: Tm Γ α.unzip)(b: Tm Γ β.unzip): Tm Γ γ.unzip :=
--   match t with
--   | .lins => Tm.cst2 (.linOp op) a b
-- def linScaleDf (t: BiLF α β γ)(op: MulOp)
--   (a: Tm Γ α.unzip)(b: Tm Γ β.unzip): Tm Γ γ.unzip :=
--   match t with
--   | .lf => (Tm.cst2 (.linScale op) a b)

-- def biArrayUnzip (T: BiOpT)[∀3BR T][t: BiArrayC T α β γ]
--   (unzip': {α' β' γ': Ty} → T α' β' γ' → Tm Γ α'.unzip → Tm Γ β'.unzip → Tm Γ γ'.unzip)
--   (a: Tm Γ α.unzip)(b: Tm Γ β.unzip): Tm Γ γ.unzip :=
--   match t.t with
--   | .array n t' =>

--     -- unzip' t' a b
--   | .base t' => unzip' t' a b


-- theorem ArithOp.unzipα (t: BiArith α β γ): α.containsTuple = false := by
--   match t with
--   | .nats => simp
--   | .flts => simp
-- theorem ArithOp.unzipβ (t: BiArith α β γ): β = β.unzip := by
--   match t with
--   | .nats => simp
--   | .flts => simp
-- theorem Ty.noTupleEqUnzip {α: Ty}(t: α.containsTuple = false): α.unzip = α := by
--   match α with
--   | .nat      => simp
--   | .idx n    => simp
--   | .flt       => simp
--   | .lin       => simp
--   | α ~> β    => simp [
--       Ty.noTupleEqUnzip (Ty.contains_arrow_a α β Ty.isTuple t),
--       Ty.noTupleEqUnzip (Ty.contains_arrow_b α β Ty.isTuple t)
--     ]
--   | α ×× β    => contradiction
--   | .ref α     => simp [
--       Ty.noTupleEqUnzip (Ty.contains_ref α Ty.isTuple t)
--     ]
--   | .unit      => simp
--   | .array n α =>
--     have r': α.containsTuple = false := (Ty.contains_array n α Ty.isTuple t)
--     have r : α.unzip = α := Ty.noTupleEqUnzip r'
--     have u: α.unzip' n = Ty.array n α := by simp[Ty.tupleMap_noTuple r']
--     have fin: α.unzip.unzip' n = Ty.array n α := by simp[r,u]
--     simp[fin]

-- -- def

def Const0.unzip: Const0 α → Tm Γ α.unzip
| .litl l => tlitl l
| .litn n => tlitn n
| .litf f => tlitf f
| .liti i (n:=n) => tliti i
| .litu   => tlitu
| .mkRef  => Tm.mkRef

def Const1.unzip (x: Tm Γ α.unzip): Const1 α β → Tm Γ β.unzip
| .suml     => Tm.cst1 Const1.suml x
| .exp      => Tm.cst1 Const1.exp x
| .sqrt     => Tm.cst1 Const1.sqrt x
| .log      => Tm.cst1 Const1.log x
| .normCdf  => Tm.cst1 Const1.normCdf x
| .fst      => Tm.cst1 Const1.fst x
| .snd      => Tm.cst1 Const1.snd x
| .sumf     => Tm.cst1 Const1.sumf x
| .i2n      => Tm.cst1 Const1.i2n x
| .n2f      => Tm.cst1 Const1.n2f x
| .refGet   => Tm.cst1 Const1.refGet x

def Const2.unzip (a: Tm Γ α.unzip)(b: Tm Γ β.unzip): Const2 α β γ → Tm Γ γ.unzip
| linOp (type:=t) op =>
  have c: BiArrays BiLin α.unzip β.unzip γ.unzip = BiArrays BiLin α β γ := sorry
  have: BiArraysC BiLin α.unzip β.unzip γ.unzip := ⟨c▸t.t⟩
  Tm.cst2 (.linOp op) a b
| linScale (type:=t) op =>
  have c: BiArray BiLF α.unzip β.unzip γ.unzip = BiArray BiLF α β γ := sorry
  have: BiArrayC BiLF α.unzip β.unzip γ.unzip := ⟨c▸t.t⟩
  Tm.cst2 (.linScale op) a b
| .arithOp (type:=t) op =>
  have c: BiArrays BiArith α.unzip β.unzip γ.unzip = BiArrays BiArith α β γ := sorry
  have: BiArraysC BiArith α.unzip β.unzip γ.unzip := ⟨c▸t.t⟩
  Tm.cst2 (.arithOp op) a b
| .addi   => Tm.cst2 .addi a b
| .maxf   => Tm.cst2 maxf a b
| .lt     => Tm.cst2 .lt a b
| .eqi    => Tm.cst2 .eqi a b
| .get (α:=α) (n:=n) => a.tupleDeMap (λ α => Ty.array n α) (Tm.cst2 .get · b)
| .tup    => Tm.cst2 .tup a b
| .refSet => Tm.cst2 .refSet a b
| .app  => a @@ b

def VPar.unzip : VPar α → VPar α.unzip := VPar.changeType
def VPar.iunzip: VPar α.unzip → VPar α := VPar.changeType

def Tm.unzip : Tm VPar α → Tm VPar α.unzip
| .err => .err
| .cst0 const0 => const0.unzip
| .cst1 const1 t => const1.unzip t.unzip
| .cst2 const2 a b => const2.unzip a.unzip b.unzip
| .abs f => fun'v x => (f x.iunzip).unzip
| .bld a (α:=α) (n:=n) =>
  let f (i: VPar (Ty.idx n)): Tm VPar α.unzip := (a i).unzip
  let rec go (α': Ty)(k: Tm VPar α.unzip → Tm VPar α'): Tm VPar (α'.unzip' n) :=
    match α' with
    | α'1 ×× α'2 => (go α'1 (Tm.fst ∘ k),, go α'2 (Tm.snd ∘ k))
    | α' =>
      have t: α'.unzip' n = Ty.array n α' := by sorry
      t▸(for'v i => (k (f i)))
  go α.unzip id
| .ite cond a b => .ite cond.unzip a.unzip b.unzip
| .var v => .var v.changeType
| .bnd rest l => .bnd rest.unzip (λ v => (l v.changeType).unzip)


open Ty
#eval! (
  let' f := fun' i:(idx 10) => tlitf 1;
  (for' i => (f @@ i))
).toAINF

#eval! (
  fun' x: (flt ×× flt).array 10 => (for' i => x[[i]].fst + x[[i]].snd )
).toAINF
