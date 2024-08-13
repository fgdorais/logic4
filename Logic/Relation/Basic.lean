/-
Copyright © 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Logic.Prelude

namespace Relation

inductive ReflGen (r : α → α → Prop) : α → α → Prop
  | incl : r x y → ReflGen r x y
  | refl (x : α) : ReflGen r x x

theorem ReflGen.rfl {r : α → α → Prop} : ReflGen r x x := refl x

inductive SymmGen (r : α → α → Prop) : α → α → Prop
  | incl : r x y → SymmGen r x y
  | inclr : r y x → SymmGen r x y

theorem SymmGen.symm {r : α → α → Prop} (h : SymmGen r x y) : SymmGen r y x := by
  cases h with
  | incl h => exact inclr h
  | inclr h => exact incl h

abbrev TransGen.incl {r : α → α → Prop} (h : r x y) : TransGen r x y := TransGen.single h

theorem TransGen.trans {r : α → α → Prop} (hl : TransGen r x y) (hr : TransGen r y z) :
    TransGen r x z := by
  induction hr with
  | single h => exact .tail hl h
  | tail _ h ih => exact .tail ih h

theorem TransGen.recAuxOn {r : α → α → Prop} {motive : (a₀ a₁ : α) → TransGen r a₀ a₁ → Prop}
    (t : TransGen r a₀ a₁) (incl : {a₀ a₁ : α} → (h : r a₀ a₁) → motive a₀ a₁ (TransGen.incl h))
    (trans : {a₀ a₁ a₂ : α} → (hl : TransGen r a₀ a₁) → (hr : TransGen r a₁ a₂) →
      (ihl : motive a₀ a₁ hl) → (ihr : motive a₁ a₂ hr) → motive a₀ a₂ (TransGen.trans hl hr)) :
    motive a₀ a₁ t := by
  induction t with
  | single h => exact incl h
  | tail ht hh ih => exact trans ht (.incl hh) ih (incl hh)

theorem TransGen.casesAuxOn {r : α → α → Prop} {motive : (a₀ a₁ : α) → TransGen r a₀ a₁ → Prop}
    (t : TransGen r a₀ a₁) (incl : {a₀ a₁ : α} → (h : r a₀ a₁) → motive a₀ a₁ (TransGen.incl h))
    (trans : {a₀ a₁ a₂ : α} → (hl : TransGen r a₀ a₁) → (hr : TransGen r a₁ a₂)
      → motive a₀ a₂ (TransGen.trans hl hr)) : motive a₀ a₁ t := by
  cases t with
  | single h => exact incl h
  | tail ht hh => exact trans ht (.incl hh)

inductive PartialEquivGen (r : α → α → Prop) : α → α → Prop
  | incl : r x y → PartialEquivGen r x y
  | inclr : r y x → PartialEquivGen r x y
  | trans : PartialEquivGen r x y → PartialEquivGen r y z → PartialEquivGen r x z

theorem PartialEquivGen.symm {r : α → α → Prop} (h : PartialEquivGen r x y) :
    PartialEquivGen r y x := by
  induction h with
  | incl h => exact inclr h
  | inclr h => exact incl h
  | trans _ _ ih₁ ih₂ => exact trans ih₂ ih₁

inductive EquivGen (r : α → α → Prop) : α → α → Prop
  | refl (x) : EquivGen r x x
  | incl : r x y → EquivGen r x y
  | inclr : r y x → EquivGen r x y
  | trans : EquivGen r x y → EquivGen r y z → EquivGen r x z

theorem EquivGen.rfl {r : α → α → Prop} : EquivGen r x x := refl x

theorem EquivGen.symm {r : α → α → Prop} (h : EquivGen r x y) :
    EquivGen r y x := by
  induction h with
  | refl x => exact refl x
  | incl h => exact inclr h
  | inclr h => exact incl h
  | trans _ _ ih₁ ih₂ => exact trans ih₂ ih₁
