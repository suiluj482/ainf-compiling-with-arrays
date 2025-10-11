-- ListMap key value pairs in ordered list

-- value type depends on key -------------------
-- element Type
abbrev DListMap.eT (α: Type u)(β : α → Type v) := Sigma β
abbrev DListMap (α : Type u)(β : α → Type v) := List (DListMap.eT α β)
def DListMap.get? [DecidableEq α](k: α)(m: DListMap α β): Option (β k) :=
  m.findSome? (λ ⟨γ, v⟩ => if t: γ = k then some (t▸v) else none)

def DListMap.groupByKey [DecidableEq α][Inhabited α][∀ γ:α, Inhabited (β γ)](m: DListMap α β): DListMap α (List ∘ β) :=
  List.splitBy (λ ⟨k,v⟩ ⟨k',v'⟩ => k==k') m -- todo only finds adjacent, vorher sortieren
  |>.map (λ l =>
    if ne' : l.isEmpty=false then
      have ne: l≠[] := by rw[←List.isEmpty_eq_false_iff]; exact ne'
      let ⟨k,_⟩ := l.head ne
      ⟨k, l.map (λ ⟨k',v⟩ => if t: k=k' then (t▸v) else panic! "key mus be same")⟩
    else
      have: Inhabited (Sigma (List ∘ β)) := ⟨Inhabited.default, []⟩
      panic! "at least one ele with key must exist"
  )

-- theorem DListMap.groupByKey_list_non_empty [DecidableEq α][∀ γ:α, DecidableEq (β γ)][Inhabited α][∀ γ:α, Inhabited (β γ)](m: DListMap α β):
--   ∀ x, List.contains m.groupByKey x → x.snd ≠ [] := sorry

----------------------------
def ListMap (Key Value: I → Type) := List ((index : I) × Key index × Value index)
def ListMap.lookup [DecidableEq I][∀ x:I, BEq (K x)] : ListMap K V → K α → Option (V α)
  | [],          _ => none
  | ⟨β,k,v⟩::ys, i => if h: β=α then if h▸ k == i then some (h▸v)
                      else lookup ys i else lookup ys i
def ListMap.lookup! [DecidableEq I][∀ x:I, BEq (K x)][∀ x:I, Inhabited (V x)] : ListMap K V → K α → V α :=
  (λ l k => ListMap.lookup l k |>.get!)
