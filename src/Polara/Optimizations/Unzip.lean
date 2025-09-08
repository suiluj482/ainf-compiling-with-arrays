import Polara.Syntax.Index
import Polara.Optimizations.NbE

@[reducible]
def Ty.isTupple: Ty → Bool := (λ | _ ×× _ => true | _ => false)
@[reducible]
def Ty.containsTupple: Ty → Bool := (Ty.contains · Ty.isTupple)


@[reducible]
def Ty.tuppleMap (f: Ty → Ty): Ty → Ty
| α ×× β => α.tuppleMap f ×× β.tuppleMap f
| α => f α

theorem Ty.tuppleMap_noTupple {α: Ty}(h: α.containsTupple = false): α.tuppleMap f = f α := by
  match α with
  | _ ×× _ => contradiction
  | α => sorry

def Tm.tuppleMap (f: Ty → Ty)(g: {α': Ty} → Tm Γ α' → Tm Γ (f α'))
  (x: Tm Γ α): Tm Γ (α.tuppleMap f) :=
  match α with
  | α ×× β => (x.fst.tuppleMap f g,, x.snd.tuppleMap f g)
  | α =>
    have t: Ty.tuppleMap f α = f α := by sorry
    t▸(g x)

def Tm.tuppleDeMap (f: Ty → Ty)(g: {α': Ty} → Tm Γ (f α') → Tm Γ α')
  (x: Tm Γ (α.tuppleMap f)): Tm Γ α :=
  match α with
  | α ×× β => (x.fst.tuppleDeMap f g,, x.snd.tuppleDeMap f g)
  | α =>
    have t: Ty.tuppleMap f α = f α := by sorry
    g (t▸x)

@[reducible]
def Ty.unzip' (n: Nat): Ty → Ty := Ty.tuppleMap (λ α => Ty.array n α)

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

#eval (Ty.array 10 (Ty.flt ×× Ty.flt)).unzip
#eval (Ty.array 10 (Ty.flt ×× Ty.flt ×× Ty.flt)).unzip
#eval (Ty.array 10 (Ty.array 10 (Ty.flt ×× Ty.flt))).unzip
#eval (Ty.array 10 (Ty.array 10 (Ty.flt ×× Ty.flt ×× Ty.flt))).unzip

-- def Tm.tuppleZipWith {α β γ: Ty}(f: Ty → Ty)(g: {α' β' γ': Ty} → Tm Γ α' → Tm Γ β' → Tm Γ γ')
--   (a: Tm Γ (α.tuppleMap f))(b: Tm Γ (β.tuppleMap f)): Tm Γ (γ.tuppleMap f) :=
--   match α with asdfsad
--   | α ×× β => (Tm.tuppleZipWith f g a.fst b.fst,, Tm.tuppleZipWith f g a.snd b.snd)
--   | α =>
--     have t: Ty.tuppleMap f α = f α := by sorry
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


-- theorem ArithOp.unzipα (t: BiArith α β γ): α.containsTupple = false := by
--   match t with
--   | .nats => simp
--   | .flts => simp
-- theorem ArithOp.unzipβ (t: BiArith α β γ): β = β.unzip := by
--   match t with
--   | .nats => simp
--   | .flts => simp
-- theorem Ty.noTuppleEqUnzip {α: Ty}(t: α.containsTupple = false): α.unzip = α := by
--   match α with
--   | .nat      => simp
--   | .idx n    => simp
--   | .flt       => simp
--   | .lin       => simp
--   | α ~> β    => simp [
--       Ty.noTuppleEqUnzip (Ty.contains_arrow_a α β Ty.isTupple t),
--       Ty.noTuppleEqUnzip (Ty.contains_arrow_b α β Ty.isTupple t)
--     ]
--   | α ×× β    => contradiction
--   | .ref α     => simp [
--       Ty.noTuppleEqUnzip (Ty.contains_ref α Ty.isTupple t)
--     ]
--   | .unit      => simp
--   | .array n α =>
--     have r': α.containsTupple = false := (Ty.contains_array n α Ty.isTupple t)
--     have r : α.unzip = α := Ty.noTuppleEqUnzip r'
--     have u: α.unzip' n = Ty.array n α := by simp[Ty.tuppleMap_noTupple r']
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
| .get (α:=α) (n:=n) => a.tuppleDeMap (λ α => Ty.array n α) (Tm.cst2 .get · b)
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
).unzip

#eval! (
  fun' x: (flt ×× flt).array 10 => (for' i => x[[i]].fst + x[[i]].snd )
).unzip.normVPar
