import Polara.Utils.Time

inductive Pipeline: Type → Type → Type 2
| nil [ToString α]: Pipeline α α
| cons [toString: ToString γ]: (String × (β → γ)) → Pipeline α β → Pipeline α γ

namespace Pipeline

  def run (a: α): Pipeline α β → β
  | nil => a
  | cons (_, f) p' => f (p'.run a)

  def runMeta (a: α): Pipeline α β → (β × List (String × String))
  | nil => (a, [])
  | cons (name, f) p' (toString:=toString) =>
      let (b, meta) := (p'.runMeta a)
      let c := f b
      (c, meta.concat (name, toString.toString c))

  def runMetaT (a: α): Pipeline α β → IO (β × List (String × String × Float))
  | nil => return (a, [])
  | cons (name, f) p' (toString:=toString) => do
      let (b, meta) ← (p'.runMetaT a)
      let (c, t) ← benchmark b f
      return (c, meta.concat (name, toString.toString c, t))

end Pipeline

inductive PipelineM (Γ: Type)(Δ: Type): Type → Type → Type 2
| nil: PipelineM Γ Δ α α
| cons (toMeta: Γ → γ → Float → IO Δ): (β → γ) → PipelineM Γ Δ α β → PipelineM Γ Δ α γ

namespace PipelineM

  def run (a: α): PipelineM Γ Δ α β → β
  | nil => a
  | cons _ f p' => f (p'.run a)

  def runMeta (i: Γ)(a: α): PipelineM Γ Δ α β → IO (β × List Δ)
  | nil => return (a, [])
  | cons toMeta f p' => do
      let (b, meta) ← (p'.runMeta i a)
      let (c, t) ← benchmark b f
      let s ← toMeta i c t
      return (c, meta.concat s)

end PipelineM
