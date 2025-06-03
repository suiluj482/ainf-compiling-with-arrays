-- List of key, value pairs, which types depend on an index Type
def ListMap (Key Value: I → Type) := List ((index : I) × Key index × Value index)
def ListMap.lookup [DecidableEq I][∀ x:I, BEq (K x)] : ListMap K V → K α → Option (V α)
  | [],          _ => none
  | ⟨β,k,v⟩::ys, i => if h: β=α then if h▸ k == i then some (h▸v)
                      else lookup ys i else lookup ys i
