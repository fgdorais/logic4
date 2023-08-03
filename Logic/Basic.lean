import Logic.Prelude

namespace Logic

/-- `Implies` connective -/
abbrev Implies (a b : Prop) : Prop := a → b

/-- `Forall` quantifier -/
abbrev Forall (α : Type _) (p : α → Prop) : Prop := ∀ x, p x

/-- `NOr` connective -/
abbrev NOr (a b : Prop) : Prop := ¬(a ∨ b)

theorem nor_of_not_of_not : ¬a → ¬b → NOr a b
  | h, _, .inl ha => h ha
  | _, h, .inr hb => h hb

theorem not_left_of_nor : NOr a b → ¬a := flip fun ha h => h (.inl ha)

theorem not_right_of_nor : NOr a b → ¬b := flip fun hb h => h (.inr hb)

theorem nor_iff_not_and_not : NOr a b ↔ ¬a ∧ ¬b :=
  ⟨fun h => ⟨not_left_of_nor h, not_right_of_nor h⟩, fun ⟨ha, hb⟩ => nor_of_not_of_not ha hb⟩

/-- `NAnd` connective -/
abbrev NAnd (a b : Prop) : Prop := ¬(a ∧ b)

theorem nand_of_not_left : ¬a → NAnd a b | ha, h => ha h.1

theorem nand_of_not_right : ¬b → NAnd a b | hb, h => hb h.2

theorem nand_resolve_left : NAnd a b → a → ¬b := fun h ha hb => h ⟨ha, hb⟩

theorem nand_resolve_right : NAnd a b → b → ¬a := fun h ha hb => h ⟨hb, ha⟩

/-- Conjunction of a list of propositions -/
inductive All : List Prop → Prop
| nil : All []
| cons : a → All as → All (a :: as)

abbrev All.head : All (a :: as) → a | cons h _ => h

abbrev All.tail : All (a :: as) → All as | cons _ h => h

theorem all_nil_eq : All [] = True :=
  propext ⟨fun _ => trivial, fun _ => All.nil⟩

theorem all_cons_eq (a as) : All (a :: as) = (a ∧ All as) :=
  propext ⟨fun | .cons hh ht => ⟨hh, ht⟩, fun ⟨hh, ht⟩ => .cons hh ht⟩

/-- Disjunction of a list of propositions -/
inductive Any : List Prop → Prop
| head : a → Any (a :: as)
| tail : Any as → Any (a :: as)

theorem any_nil_eq : Any [] = False :=
  propext ⟨fun ., False.elim⟩

theorem any_cons_eq (a as) : Any (a :: as) = (a ∨ Any as) :=
  propext ⟨fun | .head h => .inl h | .tail h => .inr h, fun | .inl h => .head h | .inr h => .tail h⟩
