import Logic.Prop.Classes
import Logic.Prop.Tactics

theorem And.deMorgan [Logic.WeaklyComplemented a] [Logic.WeaklyComplemented b] : ¬(a ∧ b) → ¬a ∨ ¬b := by
  intro h; by_cases a, b using WeaklyComplemented with
  | .isFalse ha, _ => exact .inl ha
  | _, .isFalse hb => exact .inr hb
  | .isIrrefutable ha, .isIrrefutable hb =>
    absurd ha; intro ha
    absurd hb; intro hb
    apply h; constructor
    · exact ha
    · exact hb

namespace Logic

theorem nand_iff_not_or_not [WeaklyComplemented a] [WeaklyComplemented b] : ¬(a ∧ b) ↔ ¬a ∨ ¬b :=
  ⟨And.deMorgan, fun | .inl ha, h => ha h.1 | .inr hb, h => hb h.2⟩

