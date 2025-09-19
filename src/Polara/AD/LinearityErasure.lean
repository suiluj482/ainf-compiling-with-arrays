import Polara.Syntax.All

-- linearity erasure
-- linErase
@[reducible]
def Ty.le: Ty → Ty :=
  Ty.transform (λ
  | .lin => .flt
  | α => α)
def Const0.le: Const0 α → Const0 α.le
| .litl l => .litf l
| .litn n => .litn n
| .litf f => .litf f
| .liti i => .liti i
| .litu => .litu
| .mkRef => .mkRef

def Const1.le: Const1 α β → Const1 α.le β.le
| .suml => .sumf
| .exp => .exp
| .sqrt => .sqrt
| .log => .log
| .normCdf => .normCdf
| .fst => .fst
| .snd => .snd
| .sumf => .sumf
| .i2n => .i2n
| .n2f => .n2f
| .refGet => .refGet

def Const2.le: Const2 α β γ → Const2 α.le β.le γ.le
| linOp (type:=t) op =>
  have: BiArraysC BiArith α.le β.le γ.le := ⟨
    let rec goO {α β γ: Ty}: BiArrays BiLin α β γ → BiArrays BiArith α.le β.le γ.le
    | .array n t' => .array n (goO t')
    | .base t' => .base (match t' with | .lins => .flts)
    goO t.t⟩
  (.arithOp op.toArith)
| linScale (type:=t) op =>
  have: BiArraysC BiArith α.le β.le γ.le := ⟨
    let goS {α β γ: Ty}: BiLF α β γ → BiArith α.le β.le γ.le := λ | .lf => .flts
    match t.t with
    | .array n t' => .array n (.base (goS t'))
    | .base t' => .base (goS t')
  ⟩
  (.arithOp op.toArith)
| .arithOp (type:=t) op =>
  have: BiArraysC BiArith α.le β.le γ.le := ⟨
    let rec goA {α β γ: Ty}: BiArrays BiArith α β γ → BiArrays BiArith α.le β.le γ.le
    | .array n t' => .array n (goA t')
    | .base t' => .base (match t' with | .nats => .nats | .flts => .flts)
    goA t.t⟩
  (.arithOp op)
| .addi => .addi
| .maxf => maxf
| .lt => .lt
| .eqi => .eqi
| .get => .get
| .tup => .tup
| .app => .app
| .refSet => .refSet

def Tm.le : Tm VPar α → Tm VPar α.le
| .err => .err
| .cst0 const0 => Tm.cst0 const0.le
| .cst1 const1 t => Tm.cst1 const1.le t.le
| .cst2 const2 a b => Tm.cst2 const2.le a.le b.le
| .abs f => .abs (λ x => (f x.changeType).le)
| .bld a => .bld (λ idx => (a idx).le)
| .ite cond a b => .ite cond.le a.le b.le
| .var v => .var v.changeType
| .bnd rest l => .bnd rest.le (λ v => (l v.changeType).le)

def AINF.le: AINF α → AINF α.le
| (bnds, ret) => (bnds.map (λ ⟨⟨α,v⟩,env,prim⟩ =>
  ⟨⟨α.le,v.changeType⟩,env.map (λ
  | .func α x => .func α.le x.changeType
  | .forc n i => .forc n i -- idx does not change
  | .itec i b => .itec i b -- nat does not change
  ),match prim with
  | .cst0 const0 => .cst0 const0.le
  | .cst1 const1 t => .cst1 const1.le t.changeType
  | .cst2 const2 a b => .cst2 const2.le a.changeType b.changeType
  | .err => .err
  | .var v => .var v.changeType
  | .abs x y => .abs x.changeType y.changeType
  | .bld i x => .bld i x.changeType
  | .ite cond a b => .ite cond.changeType a.changeType b.changeType
  ⟩
), ret.changeType)
