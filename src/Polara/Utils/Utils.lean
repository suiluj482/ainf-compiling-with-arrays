import Polara.Utils.Print

-----
abbrev Some (F: α → Type u) := (γ: α) × F γ
def Some.of (f: F α): Some F := ⟨α, f⟩
instance [Inhabited α][∀ γ:α, Inhabited (F γ)]: Inhabited (Some F) :=
  ⟨Inhabited.default,Inhabited.default⟩
instance [DecidableEq α][∀ γ, DecidableEq (F γ)]: DecidableEq (@Some α F) :=
  λ ⟨γ,f⟩ ⟨γ',f'⟩ => if t: γ = γ' then
    if t': t▸f=f' then
      isTrue (by subst t; simp[t'])
    else
      isFalse (by subst t; simp[t'])
  else
    isFalse (by simp[t])
instance [DecidableEq α][∀ γ, BEq (F γ)]: BEq (@Some α F) :=
  ⟨λ ⟨γ,f⟩ ⟨γ',f'⟩ => if t: γ = γ' then t▸ f == f' else false⟩
instance [Hashable α][∀ γ: α, Hashable (F γ)]: Hashable (@Some α F) :=
  ⟨λ ⟨γ,f⟩ => mixHash (Hashable.hash γ) (Hashable.hash f)⟩
-- instance [DecidableEq α][LawfulBEq α]
--   [∀ γ, BEq (F γ)][∀ γ, LawfulBEq (F γ)]
--   [BEq (Some F)]: LawfulBEq (@Some α F) where
--   eq_of_beq {a b} h := sorry
--   rfl {a} := match a with
--     | ⟨α,v⟩ =>
--       have t: α == α := by simp
--       have t': v == v := by simp
--       by simp[t,t']

instance [Inhabited α][∀ γ:α, Inhabited (F γ)]: Inhabited (Sigma F) :=
  ⟨Inhabited.default,Inhabited.default⟩
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
