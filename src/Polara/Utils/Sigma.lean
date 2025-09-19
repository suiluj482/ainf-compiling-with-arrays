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
instance {α: Type u}{β: α → Type v}[DecidableEq (Sigma β)]
  : LawfulBEq (Sigma β) where
  eq_of_beq := by simp
