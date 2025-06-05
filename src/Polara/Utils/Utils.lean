import Polara.Utils.Print

-- ListMap -----------------------------------------------------------------------------------
-- List of key, value pairs, which types depend on an index Type
def ListMap (Key Value: I → Type) := List ((index : I) × Key index × Value index)
def ListMap.lookup [DecidableEq I][∀ x:I, BEq (K x)] : ListMap K V → K α → Option (V α)
  | [],          _ => none
  | ⟨β,k,v⟩::ys, i => if h: β=α then if h▸ k == i then some (h▸v)
                      else lookup ys i else lookup ys i

-----
def Some (F: α → Type u) := (γ: α) × F γ

---
instance TrivialInhabited (a: α): Inhabited α := ⟨a⟩

---
def Prod.mapBoth (p: (α × α))(f: α → β): β × β := (f p.1, f p.2)
def Prod.map3 (p: (α × α × α))(f: α → β): β × β × β := (f p.1, f p.2.1, f p.2.2)
def Prod.all3 (p: (α × α × α))(f: α → Bool): Bool := (f p.1 && f p.2.1 && f p.2.2)
def Prod.zip: (α × β) → (α' × β') → ((α × α') × (β × β')) :=
  fun (a, b) (a', b') => ((a, a'), (b, b'))

-- HList
inductive HList: List (Type u) → Type (u+1)
| nil: HList []
| cons {as: List (Type u)} {α: (Type u)} (a: α) (prev: HList as): HList (α :: as)
