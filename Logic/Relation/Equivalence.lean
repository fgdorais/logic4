/-
Copyright © 2023-2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Logic.Relation.Classes
import Logic.Relation.Tactics
import Logic.Relation.Order

open Logic

namespace Relation
variable {α} (r : α → α → Prop)

class abbrev PartialEquivalence : Prop := Symmetric r, Euclidean r

instance [PartialEquivalence r] : Transitive r := Euclidean.toTransitive r

abbrev inferPartialEquivalence [Symmetric r] [Euclidean r] : PartialEquivalence r where
  symm := Symmetric.symm
  eucl := Euclidean.eucl

open Relation in
instance [Symmetric r] : PartialEquivalence (TransGen r) := .mk

namespace PartialEquivalence
variable {r} [PartialEquivalence r]

protected theorem trans {x y z} : r x y → r y z → r x z := Transitive.trans

end PartialEquivalence

class abbrev Equivalence : Prop := Reflexive r, Euclidean r

instance [Equivalence r] : PartialEquivalence r := .mk

abbrev inferEquivalence {α} (r : α → α → Prop) [Reflexive r] [Euclidean r] : Equivalence r := .mk

namespace Equivalence
variable {r} [Equivalence r]

protected theorem symm {x y} : r x y → r y x := Symmetric.symm
protected theorem trans {x y z} : r x y → r y z → r x z := Transitive.trans

end Equivalence

protected def Equivalence.to_eqv [Equivalence r] : _root_.Equivalence r where
  refl := Reflexive.refl
  symm := Symmetric.symm
  trans := Transitive.trans

instance (α) : Equivalence (α:=α) (.=.) := .mk
instance (α) [Setoid α] : Equivalence (α:=α) (.≈.) := .mk
instance (α) [Setoid α] : Equivalence (α:=α) Setoid.r := .mk

open Relation in
instance [Reflexive r] [Symmetric r] : Equivalence (TransGen r) := .mk

abbrev PartialEquivalence.toSubtype [PartialEquivalence r] : { x // r x x } → { x // r x x } → Prop
| ⟨x,_⟩, ⟨y,_⟩ => r x y

instance [PartialEquivalence r] : Equivalence (PartialEquivalence.toSubtype r) where
  refl := Subtype.property
  eucl := Euclidean.eucl (r:=r)

class abbrev Apartness : Prop := Symmetric r, Comparison r, Reflexive (¬r . .)
instance [self : Apartness r] : Irreflexive r := ⟨by intro; reflexivity using (¬r . .)⟩

abbrev inferApartness [Irreflexive r] [Symmetric r] [Comparison r] : Apartness r := .mk

instance [Apartness r] : Equivalence (¬ r . .) where
  refl := Irreflexive.irrefl
  eucl {x _ _} nxy nxz hyz :=
    match Comparison.compare hyz x with
    | .inl hyx => nxy (Symmetric.symm hyx)
    | .inr hxz => nxz hxz

def Equivalence.toApartness [Equivalence r] [ComplementedRel r] : Apartness (¬ r . .) where
  refl x h := h (Reflexive.refl x)
  symm nxy hyx := nxy (Symmetric.symm hyx)
  compare {x y} (nxy z) := by
    by_cases r x z, r z y using Complemented with
    | .isFalse nxz, _ =>
      left
      exact nxz
    | _, .isFalse nzy =>
      right
      exact nzy
    | .isTrue hxz, .isTrue hzy =>
      absurd nxy
      transitivity z
      exact hxz
      exact hzy

class TightApartness : Prop extends Apartness r where
  protected tight {x y} : ¬r x y → x = y

namespace TightApartness

theorem eq_iff_not_apart {α} {r : α → α → Prop} [TightApartness r] (x y : α) : x = y ↔ ¬ r x y := by
  constructor
  · intro | rfl => irreflexivity
  · exact TightApartness.tight

end TightApartness

instance [ComplementedEq α] : TightApartness (α:=α) (.≠.) where
  toApartness := Equivalence.toApartness _
  tight := Stable.by_contradiction
