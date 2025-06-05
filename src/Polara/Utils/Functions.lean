import Polara.Utils.Utils

namespace Func

  def zip (f: α → β)(g: α → γ): α → (β × γ) :=
    (fun a => (f a, g a))

  def mapScdParam (f: α → β → γ)(g: δ → β): α → δ → γ :=
    (fun a b => f a (g b))

  def mapSetScdParam (f: α → β → γ)(b: β): α → γ :=
    (fun a => f a b)

  def set2Param (f: α → β → γ)(b: β): α → γ :=
    (fun a => f a b)

  def set3Param (f: α → Θ → β → γ)(b: β): α → Θ → γ :=
    (fun a t => f a t b)

  def set4Param (f: α → Θ → Ω → β → γ)(b: β): α → Θ → Ω → γ :=
    (fun a t o => f a t o b)

  def pure {β: Type u} (val: α): β → α :=
    Function.const β val

  def mapPure {β: Type u}  (f: α → γ): α → β → γ :=
    (fun a _ => f a)

  def tuple (f: α → β → γ): (α × β) → γ :=
    (fun (a, b) => f a b)

  def detuple (f: (α × β) → γ): α → β → γ :=
    (fun a b => f (a, b))

  def swap (f: α → β → γ): β → α → γ :=
   (fun b a => f a b)

  def chain2 (g: β → γ)(f: α → δ → β): α → δ → γ :=
    (g ∘ ·) ∘ f

  def chain3 (g: β → γ)(f: α → δ → θ → β): α → δ → θ → γ :=
    (fun a b c => g <| f a b c)

  def zipWith (f: β → γ → δ)(g: α → β)(h: α → γ): α → δ :=
    (tuple f) ∘ (zip g h)

end Func
