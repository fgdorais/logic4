/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Logic.Proposition.Classes
import Logic.Proposition.Tactics

namespace Logic

/-! ## Not -/

alias not_not_elim := Stable.by_contradiction

/-! ## And -/

alias and_left := And.left
alias and_right := And.right
alias and_intro := And.intro
alias and_elim := And.elim

theorem and_deMorgan [WeaklyComplemented a] [WeaklyComplemented b] : ¬(a ∧ b) → ¬a ∨ ¬b := by
  intro h; by_cases a, b using WeaklyComplemented with
  | .isFalse ha, _ => exact .inl ha
  | _, .isFalse hb => exact .inr hb
  | .isIrrefutable ha, .isIrrefutable hb =>
    absurd ha; intro ha
    absurd hb; intro hb
    apply h; constructor
    · exact ha
    · exact hb

theorem and_deMorgan_left [Complemented a] : ¬(a ∧ b) → ¬a ∨ ¬b := by
  intro h; by_cases a using Complemented with
  | .isFalse ha => exact .inl ha
  | .isTrue ha =>
    right; intro hb
    apply h; constructor
    · exact ha
    · exact hb

theorem and_deMorgan_right [Complemented b] : ¬(a ∧ b) → ¬a ∨ ¬b := by
  intro h; by_cases b using Complemented with
  | .isFalse hb => exact .inr hb
  | .isTrue hb =>
    left; intro ha
    apply h; constructor
    · exact ha
    · exact hb

/-! ## Or -/

alias or_left := Or.inl
alias or_right := Or.inr
alias or_elim := Or.elim
alias or_resolve_left := Or.resolve_left
alias or_resolve_right := Or.resolve_right

theorem or_deMorgan : ¬(a ∨ b) → ¬a ∧ ¬b := by
  intro h; constructor
  · intro ha; exact h (.inl ha)
  · intro hb; exact h (.inr hb)

/-! ## Iff -/

theorem iff_mt : (a ↔ b) → (¬a ↔ ¬b)
  | ⟨hab, hba⟩ => ⟨mt hba, mt hab⟩

theorem iff_mtr [Stable a] [Stable b] : (¬a ↔ ¬b) → (a ↔ b)
  | ⟨hab, hba⟩ => ⟨Stable.by_contrapositive hba, Stable.by_contrapositive hab⟩

theorem not_iff_not [Stable a] [Stable b] : (¬a ↔ ¬b) ↔ (a ↔ b) :=
  ⟨iff_mtr, iff_mt⟩

/-! ## NOr -/

theorem nor_of_not_of_not : ¬a → ¬b → ¬(a ∨ b)
  | h, _, .inl ha => h ha
  | _, h, .inr hb => h hb

theorem not_left_of_nor : ¬(a ∨ b) → ¬a :=
  flip fun ha h => h (.inl ha)

theorem not_right_of_nor : ¬(a ∨ b) → ¬b :=
  flip fun hb h => h (.inr hb)

theorem nor_iff_not_and_not : ¬(a ∨ b) ↔ ¬a ∧ ¬b :=
  ⟨fun h => ⟨not_left_of_nor h, not_right_of_nor h⟩, fun ⟨ha, hb⟩ => nor_of_not_of_not ha hb⟩

/-! ## NAnd -/

theorem nand_of_not_left : ¬a → ¬(a ∧ b)
  | ha, ⟨h, _⟩ => ha h

theorem nand_of_not_right : ¬b → ¬(a ∧ b)
  | hb, ⟨_, h⟩  => hb h

theorem nand_resolve_left : ¬(a ∧ b) → a → ¬b
  | h, ha, hb => h ⟨ha, hb⟩

theorem nand_resolve_right : ¬(a ∧ b) → b → ¬a
  | h, ha, hb => h ⟨hb, ha⟩

theorem nand_iff_not_or_not [WeaklyComplemented a] [WeaklyComplemented b] : ¬(a ∧ b) ↔ ¬a ∨ ¬b :=
  ⟨and_deMorgan, fun | .inl ha, ⟨h, _⟩ => ha h | .inr hb, ⟨_, h⟩ => hb h⟩
