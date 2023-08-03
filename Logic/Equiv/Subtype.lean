import Logic.Equiv.Basic

namespace Subtype
variable {α₁ α₂ : Sort _} {p₁ : α₁ → Prop} {p₂ : α₂ → Prop}

protected def equiv (e : Equiv α₁ α₂) (h : ∀ x, p₁ x ↔ p₂ (e.fwd x)) : Equiv { x // p₁ x } { x // p₂ x} where
  fwd | ⟨x₁, h₁⟩ => ⟨e.fwd x₁, (h x₁).mp h₁⟩
  rev | ⟨x₂, h₂⟩ => ⟨e.rev x₂, (h (e.rev x₂)).mpr ((e.fwd_rev x₂).symm ▸ h₂)⟩
  fwd_eq_iff_rev_eq := by intro
    | ⟨x₁, h₁⟩, ⟨x₂,h₂⟩ =>
      constructor
      · intro | rfl => ext; exact e.rev_fwd ..
      · intro | rfl => ext; exact e.fwd_rev ..

end Subtype
