import Polara.Utils.Print
import Std

instance [Inhabited β]: Inhabited (α → β) := ⟨λ _ => Inhabited.default⟩
-----
def Sigma.of (f: F α): Sigma F := ⟨α, f⟩
instance [Inhabited α][∀ γ:α, Inhabited (F γ)]
  : Inhabited (Sigma F) :=
  ⟨Inhabited.default,Inhabited.default⟩
instance [Hashable α][∀ γ: α, Hashable (F γ)]
  : Hashable (@Sigma α F) :=
  ⟨λ ⟨γ,f⟩ => mixHash (Hashable.hash γ) (Hashable.hash f)⟩

instance [DecidableEq α][∀ γ, DecidableEq (F γ)]
  : DecidableEq (@Sigma α F) :=
  λ ⟨γ,f⟩ ⟨γ',f'⟩ => if t: γ = γ' then
    if t': t▸f=f' then
      isTrue (by subst t; simp[t'])
    else
      isFalse (by subst t; simp[t'])
  else
    isFalse (by simp[t])
instance [DecidableEq (Sigma β)]
  : BEq (Sigma β) where
  beq x y := decide (x = y)

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
