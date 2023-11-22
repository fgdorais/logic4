/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Logic.Prelude

namespace Logic

/-- `Implies` connective -/
abbrev Implies (a b : Prop) : Prop := a → b

/-- `Forall` quantifier -/
abbrev Forall (α : Type _) (p : α → Prop) : Prop := ∀ x, p x

/-- `NOr` connective: `¬(a ∨ b)` -/
abbrev NOr (a b : Prop) : Prop := ¬(a ∨ b)

/-- `NAnd` connective: `¬(a ∧ b)` -/
abbrev NAnd (a b : Prop) : Prop := ¬(a ∧ b)

/-- Conjunction of a list of propositions -/
inductive All : List Prop → Prop
| nil : All []
| cons : a → All as → All (a :: as)

abbrev All.head : All (a :: as) → a
  | cons h _ => h

abbrev All.tail : All (a :: as) → All as
  | cons _ h => h

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
