import Polara.Syntax.All

-- but everything as function from an env?
-- ainf?

@[reducible]
def Ty.defunc: Ty → Ty :=
  Ty.map (λ
  | _ ~> _ => .unit
  | α => α)

-- @[reducible]
-- def Ty.defuncMeta: Ty → Type :=


#eval (.flt ×× .flt).defunc
#eval (.flt ~> .flt).defunc
#eval (.flt ×× (.flt ~> .flt)).defunc
#eval (.flt ~> (.flt ~> .flt)).defunc

def Const0.defunc: Const0 α → Tm Γ α.defunc
| .litl l => tlitl l
| .litn n => tlitn n
| .litf f => tlitf f
| .liti i => tliti i
| .litu => tlitu
| .mkRef => Tm.mkRef

def Const1.defunc (x: Tm Γ α.defunc): Const1 α β → Tm Γ β.defunc
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

def Const2.defunc (a: Tm Γ α.defunc)(b: Tm Γ β.defunc): Const2 α β γ → Tm Γ γ.defunc
| linOp (type:=t) op =>
  have: BiArraysC BiLin α.defunc β.defunc γ.defunc := ⟨
    let rec goO {α β γ: Ty}: BiArrays BiLin α β γ → BiArrays BiLin α.defunc β.defunc γ.defunc
    | .array n t' => .array n (goO t')
    | .base t' => .base (match t' with | .lins => .lins)
    goO t.t⟩
  Tm.cst2 (.linOp op) a b
| linScale (type:=t) op =>
  have: BiArrayC BiLF α.defunc β.defunc γ.defunc := ⟨
    let goS {α β γ: Ty}: BiLF α β γ → BiLF α.defunc β.defunc γ.defunc := λ | .lf => .lf
    match t.t with
    | .array n t' => .array n (goS t')
    | .base t' => .base (goS t')
  ⟩
  Tm.cst2 (.linScale op) a b
| .arithOp (type:=t) op =>
  have: BiArraysC BiArith α.defunc β.defunc γ.defunc := ⟨
    let rec goA {α β γ: Ty}: BiArrays BiArith α β γ → BiArrays BiArith α.defunc β.defunc γ.defunc
    | .array n t' => .array n (goA t')
    | .base t' => .base (match t' with | .nats => .nats | .flts => .flts)
    goA t.t⟩
  Tm.cst2 (.arithOp op) a b
| .addi   => Tm.cst2 .addi a b
| .maxf   => Tm.cst2 maxf a b
| .lt     => Tm.cst2 .lt a b
| .eqi    => Tm.cst2 .eqi a b
| .get    => Tm.cst2 .get a b
| .tup    => Tm.cst2 .tup a b
| .refSet => Tm.cst2 .refSet a b
| .app  => sorry -- complete

def Tm.defunc : Tm VPar α → Tm VPar α.defunc
| .err => .err
| .cst0 const0 => const0.defunc
| .cst1 const1 t => const1.defunc t.defunc
| .cst2 const2 a b => const2.defunc a.defunc b.defunc
| .abs f => ()'
| .bld a => .bld (λ idx => (a idx).defunc)
| .ite cond a b => .ite cond.defunc a.defunc b.defunc
| .var v => .var v.changeType
| .bnd rest l => .bnd rest.defunc (λ v => (l v.changeType).defunc)
