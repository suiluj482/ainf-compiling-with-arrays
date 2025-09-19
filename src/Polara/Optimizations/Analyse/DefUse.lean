import Polara.Syntax.All

abbrev DefUse := Std.HashMap (Some Var) (List Bnd)

def AINF.defUse: AINF α → DefUse
| (bnds, _) =>
    bnds.foldl (λ dU bnd =>
      let vars := Bnd.vars bnd
      vars.foldl (λ dU v =>
        dU.alter v (bnd :: ·.getD [])
      ) dU
    ) (.emptyWithCapacity bnds.length)

def DefUse.of (dU: DefUse)(v: Var α): (List Bnd) :=
  dU.get! ⟨_,v⟩

-- for single var, for all less efficient
def Var.uses (v: Var α)(bnds: Bnds): List Bnd :=
  bnds.filter (Bnd.vars · |>.contains ⟨_,v⟩)
