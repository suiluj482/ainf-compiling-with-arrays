import Polara.Syntax.Index

@[reducible]
def Ty.removeUnits: Ty → Option Ty
| .unit => none
| .idx n => some (.idx n)
| .lin => some .flt
| .nat => some .nat
| .flt => some .flt
| .array n α => α.removeUnits.map (.array n ·)
| α ×× β => Option.merge (· ×× ·) (α.removeUnits) (β.removeUnits)
| α ~> β => Option.merge (· ~> ·) (α.removeUnits) (β.removeUnits)
| .ref α => α.removeUnits.map (.ref ·)

-- theorem

-- remove Vars of type Unit?
def Tm.removeUnits (ok: α.removeUnits.isSome)(t: Tm VPar α): (Tm VPar (α.removeUnits.get ok)) :=
match α, t with
| _, .err => .err
| _, .var i => .var i.changeType
| _, .abs (α:=α) (β:=β) f => sorry
| _, .bld (α:=α) f => sorry
| _, .ite c t e => sorry
| _, .bnd (α:=α) (β:=β) t rest => sorry
| _, .cst0 k => sorry
| _, .cst1 k a => sorry
| _, .cst2 k a b => sorry
