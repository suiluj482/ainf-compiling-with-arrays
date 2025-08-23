import Polara.Syntax.Index

@[reducible]
def Ty.rmUnits: Ty → Ty
| .unit  => .unit
| .idx n => .idx n
| .lin   => .lin
| .nat   => .nat
| .flt   => .flt
| .array n α => match α.rmUnits with
  | .unit => .unit
  | α'    => .array n α'
| α ×× β => match α.rmUnits, β.rmUnits with
  | .unit, .unit => .unit
  | .unit, β'    => β'
  | α', .unit    => α'
  | α', β'       => α' ×× β'
| α ~> β => match α.rmUnits, β.rmUnits with
  | _, .unit     => .unit
  | .unit, β'    => β'
  | α', β'       => α' ~> β'
| .ref α => match α.rmUnits with
  | .unit => .unit
  | α'    => .ref α'

def Const0.rmUnits: Const0 α → Tm Γ α.rmUnits
| .litn n => tlitn n
| .litf f => tlitf f
| .liti i => tliti i
| .litl l => tlitl l
| .litu => tlitu
| mkRef (α:=α') => if h: α'.rmUnits = .unit then
    have t: α'.ref.rmUnits = .unit := by simp[Ty.rmUnits, h]
    t▸()'
  else
    have t: α'.ref.rmUnits = α'.rmUnits.ref := by simp[Ty.rmUnits, h]
    t▸Tm.cst0 .mkRef

def Const1.rmUnits (x: Tm Γ α.rmUnits): Const1 α β → Tm Γ β.rmUnits
| .exp     => Tm.cst1 Const1.exp x
| .sqrt    => Tm.cst1 Const1.sqrt x
| .normCdf => Tm.cst1 Const1.normCdf x
| .log     => Tm.cst1 Const1.log x
| .fst (α:=α') (β:=β') => if h: α'.rmUnits = .unit then
    h▸()'
  else
    if h': β'.rmUnits = .unit then
      have t: (α'××β').rmUnits = α'.rmUnits := by simp[Ty.rmUnits, h']
      t▸x
    else
      have t: (α'××β').rmUnits = (α'.rmUnits××β'.rmUnits) := by simp[Ty.rmUnits, h']
      Tm.cst1 Const1.fst (t▸x)
| .snd (α:=α') (β:=β') => if h: β'.rmUnits = .unit then
    h▸()'
  else
    if h': α'.rmUnits = .unit then
      have t: (α'××β').rmUnits = β'.rmUnits := by simp[Ty.rmUnits, h']
      t▸x
    else
      have t: (α'××β').rmUnits = (α'.rmUnits××β'.rmUnits) := by simp[Ty.rmUnits, h']
      Tm.cst1 Const1.snd (t▸x)
| .sumf    => Tm.cst1 Const1.sumf x
| .suml    => Tm.cst1 Const1.suml x
| .i2n     => Tm.cst1 Const1.i2n x
| .n2f     => Tm.cst1 Const1.n2f x
| refGet (α:=α') => if h: α'.rmUnits = .unit then
    h▸()'
  else
    have t: α'.ref.rmUnits = α'.rmUnits.ref := by simp[Ty.rmUnits, h]
    Tm.cst1 Const1.refGet (t▸x)

def ArithOp.rmUnits [t: BiArraysC BiArith α β γ](op: ArithOp)
  (a: Tm Γ α.rmUnits)(b: Tm Γ β.rmUnits): Tm Γ γ.rmUnits :=
   match t.t with
  | .array n t' (α:=α') (β:=β') (γ:=γ') =>
      have: BiArraysC BiArith _ _ _ := ⟨t'⟩
      if h: γ'.rmUnits = .unit then
        have t: (Ty.array n γ').rmUnits = .unit := by simp[Ty.rmUnits, h]
        t▸()'
      else
        let a' (i: Tm Γ (.idx n)): Tm Γ α'.rmUnits := if h': α'.rmUnits = .unit then
            h'▸()'
          else
            have t: (Ty.array n α').rmUnits = Ty.array n α'.rmUnits := by simp[Ty.rmUnits, h, h']
            (t▸a)[[i]]
        let b' (i: Tm Γ (.idx n)): Tm Γ β'.rmUnits := if h': β'.rmUnits = .unit then
            h'▸()'
          else
            have t: (Ty.array n β').rmUnits = Ty.array n β'.rmUnits := by simp[Ty.rmUnits, h, h']
            (t▸b)[[i]]

        have t: (Ty.array n γ').rmUnits = Ty.array n γ'.rmUnits := by simp[Ty.rmUnits, h]
        t▸for' i => (ArithOp.rmUnits op (a' i) (b' i))
  | .base t' => match t' with
    | .nats => Tm.cst2 (.arithOp op) a b
    | .flts => Tm.cst2 (.arithOp op) a b
def linOpRmUnits [t: BiArraysC BiLin α β γ](op: AddOp)
  (a: Tm Γ α.rmUnits)(b: Tm Γ β.rmUnits): Tm Γ γ.rmUnits :=
  match t.t with
  | .array n t' (α:=α') (β:=β') (γ:=γ') =>
      have: BiArraysC BiLin _ _ _ := ⟨t'⟩
      if h: γ'.rmUnits = .unit then
        have t: (Ty.array n γ').rmUnits = .unit := by simp[Ty.rmUnits, h]
        t▸()'
      else
        let a' (i: Tm Γ (.idx n)): Tm Γ α'.rmUnits := if h': α'.rmUnits = .unit then
            h'▸()'
          else
            have t: (Ty.array n α').rmUnits = Ty.array n α'.rmUnits := by simp[Ty.rmUnits, h, h']
            (t▸a)[[i]]
        let b' (i: Tm Γ (.idx n)): Tm Γ β'.rmUnits := if h': β'.rmUnits = .unit then
            h'▸()'
          else
            have t: (Ty.array n β').rmUnits = Ty.array n β'.rmUnits := by simp[Ty.rmUnits, h, h']
            (t▸b)[[i]]

        have t: (Ty.array n γ').rmUnits = Ty.array n γ'.rmUnits := by simp[Ty.rmUnits, h]
        t▸for' i => (linOpRmUnits op (a' i) (b' i))
  | .base t' => match t' with
    | .lins => Tm.cst2 (.linOp op) a b
def linScaleRmUnits [t: BiArrayC BiLF α β γ](op: MulOp)
  (a: Tm Γ α.rmUnits)(b: Tm Γ β.rmUnits): Tm Γ γ.rmUnits :=
  let go {α' β' γ'}[t: BiLFC α' β' γ'](a: Tm Γ α'.rmUnits)(b: Tm Γ β'.rmUnits): Tm Γ γ'.rmUnits :=
    match t.t with
    | .lf => (Tm.cst2 (.linScale op) a b)

  match t.t with
  | .array n t' (α:=α') (β:=β') (γ:=γ') =>
      have: BiLFC _ _ _ := ⟨t'⟩
      if h: γ'.rmUnits = .unit then
        have t: (Ty.array n γ').rmUnits = .unit := by simp[Ty.rmUnits, h]
        t▸()'
      else
        let a' (i: Tm Γ (.idx n)): Tm Γ α'.rmUnits := if h': α'.rmUnits = .unit then
            h'▸()'
          else
            have t: (Ty.array n α').rmUnits = Ty.array n α'.rmUnits := by simp[Ty.rmUnits, h, h']
            (t▸a)[[i]]
        let b' (i: Tm Γ (.idx n)): Tm Γ β'.rmUnits := if h': β'.rmUnits = .unit then
            h'▸()'
          else
            have t: (Ty.array n β').rmUnits = Ty.array n β'.rmUnits := by simp[Ty.rmUnits, h, h']
            (t▸b)[[i]]

        have t: (Ty.array n γ').rmUnits = Ty.array n γ'.rmUnits := by simp[Ty.rmUnits, h]
        t▸for' i => (go (a' i) (b' i))
  | .base t' =>
      have: BiLFC _ _ _ := ⟨t'⟩
      go a b

def Const2.rmUnits (a: Tm Γ α.rmUnits)(b: Tm Γ β.rmUnits): Const2 α β γ → Tm Γ γ.rmUnits
| arithOp op => op.rmUnits a b
| linOp op => linOpRmUnits op a b
| linScale op => linScaleRmUnits op a b
| .addi => Tm.cst2 (.addi) a b
| .eqi => a ==' b
| .lt => a <' b
| .maxf => Max.max a b
| .get (n:=n') (α:=α') => if h: α'.rmUnits = .unit then
    h▸()'
  else
    have t: (Ty.array n' α').rmUnits = (Ty.array n' α'.rmUnits) := by simp[Ty.rmUnits, h]
    (t▸a)[[b]]
| .tup  => if h: α.rmUnits = .unit then
    if h': β.rmUnits = .unit then
      have t: (α××β).rmUnits = .unit := by simp[Ty.rmUnits, h, h']
      t▸()'
    else
      have t: (α××β).rmUnits = β.rmUnits := by simp[Ty.rmUnits, h, h']
      t▸b
  else
    if h': β.rmUnits = .unit then
      have t: (α××β).rmUnits = α.rmUnits := by simp[Ty.rmUnits, h, h']
      t▸a
    else
      have t: (α××β).rmUnits = α.rmUnits××β.rmUnits := by simp[Ty.rmUnits, h, h']
      t▸(a,, b)
| .refSet => panic! "refSet not supported in rmUnit"
| .app (α:=α') (β:=β') => if h: β'.rmUnits = .unit then
    h▸()'
  else
    if h': α'.rmUnits = .unit then
      have t: (α'~>β').rmUnits = β'.rmUnits := by simp[Ty.rmUnits, h, h']
      t▸a
    else
      have t: (α'~>β').rmUnits = α'.rmUnits~>β'.rmUnits := by simp[Ty.rmUnits, h, h']
      t▸a @@ b
def VPar.rmUnits: VPar α → VPar α.rmUnits := VPar.changeType
def VPar.irmUnits: VPar α.rmUnits → VPar α := VPar.changeType

-- doesn't support refs
def Tm.rmUnits (t: Tm VPar α): Tm VPar α.rmUnits :=
match α, t with
| _, .err => .err
| _, .var i => .var i.rmUnits
| _, .abs (α:=α') (β:=β') f => if h: β'.rmUnits = .unit then
      have t: .unit = (α' ~> β').rmUnits := by simp[Ty.rmUnits, h]
      t▸()'
    else
      if h: α'.rmUnits = .unit then
        have t: β'.rmUnits = (α' ~> β').rmUnits := by simp[Ty.rmUnits, h]
        t▸(f Inhabited.default).rmUnits
      else
        have t: α'.rmUnits ~> β'.rmUnits = (α' ~> β').rmUnits := by simp[Ty.rmUnits, h]
        t▸fun'v x => ((f x.irmUnits).rmUnits)
| _, .bld (α:=α') f => if h: α'.rmUnits = .unit then
      have t: (Ty.array _ α').rmUnits = .unit := by simp[Ty.rmUnits, h]
      t▸()'
    else
      have t: (Ty.array _ α').rmUnits = (Ty.array _ α'.rmUnits) := by simp[Ty.rmUnits, h]
      t▸(for'v i => ((f i).rmUnits))
| _, .ite c t e => if' c then t.rmUnits else e.rmUnits
| _, .bnd (α:=α') (β:=β') t rest => if α'.rmUnits = .unit then
      (rest Inhabited.default).rmUnits
    else
      let'v x := t.rmUnits; (rest x.irmUnits).rmUnits
| _, .cst0 c     => c.rmUnits
| _, .cst1 c a   => c.rmUnits a.rmUnits
| _, .cst2 c a b => c.rmUnits a.rmUnits b.rmUnits
