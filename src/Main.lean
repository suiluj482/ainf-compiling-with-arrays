import «Polara»

def main : IO Unit :=
  IO.println s!"Success!"

#print axioms Tm.toAINF
#print axioms AINF.cse
#print axioms Tm.norm
