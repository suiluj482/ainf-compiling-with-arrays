import Polara.Syntax.All

abbrev UseDef := Std.DHashMap (Sigma Var) (λ ⟨α,_⟩ => Env × Prim α)

def AINF.useDef: AINF α → UseDef
| (bnds, _) => Std.DHashMap.ofList bnds

def UseDef.of (uD: UseDef)(v: Var α): (Env × Prim α) :=
  uD.get! ⟨_,v⟩
