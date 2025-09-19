import Polara.Utils.Print
import Std

instance [Inhabited β]: Inhabited (α → β) := ⟨λ _ => Inhabited.default⟩

---
instance TrivialInhabited (a: α): Inhabited α := ⟨a⟩

---
def Prod.mapM [Monad M] (p: (M α × M β)): M (α × β) := do return (← p.fst,←p.snd)
def Prod.mapBoth (p: (α × α))(f: α → β): β × β := (f p.1, f p.2)
def Prod.map3 (p: (α × α × α))(f: α → β): β × β × β := (f p.1, f p.2.1, f p.2.2)
def Prod.all3 (p: (α × α × α))(f: α → Bool): Bool := (f p.1 && f p.2.1 && f p.2.2)
def Prod.zip: (α × β) → (α' × β') → ((α × α') × (β × β')) :=
  fun (a, b) (a', b') => ((a, a'), (b, b'))

-- HList
inductive HList: List (Type u) → Type (u+1)
| nil: HList []
| cons {as: List (Type u)} {α: (Type u)} (a: α) (prev: HList as): HList (α :: as)
