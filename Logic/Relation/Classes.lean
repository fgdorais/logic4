/-
Copyright © 2023-2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Logic.Basic
import Logic.Proposition.Lemmas
import Logic.Relation.Basic

open Logic

namespace Relation

/-! ## Reflexivity -/

class Reflexive {α} (r : α → α → Prop) : Prop where
  protected refl (x) : r x x

protected abbrev Reflexive.rfl {α} {r : α → α → Prop} [Reflexive r] {x : α} := Reflexive.refl (r:=r) x

theorem Reflexive.of_eq {α} (r : α → α → Prop) [Reflexive r] : {x y : α} → x = y → r x y
| _, _, rfl => Reflexive.rfl

instance (α) [Setoid α] : Reflexive (α:=α) (.≈.) := ⟨Setoid.refl⟩
instance (α) [Setoid α] : Reflexive (α:=α) Setoid.r := ⟨Setoid.refl⟩
instance (α) : Reflexive (α:=α) (.≅.) := ⟨HEq.refl⟩
instance (α) : Reflexive (α:=α) (.=.) := ⟨Eq.refl⟩
instance : Reflexive (.→.) := ⟨@id⟩
instance : Reflexive (.↔.) := ⟨Iff.refl⟩

instance (r : α → α → Prop) : Reflexive (ReflGen r) := ⟨ReflGen.refl⟩

instance (r : α → α → Prop) : Reflexive (EquivGen r) := ⟨EquivGen.refl⟩

instance {α} (r : α → α → Prop) [Reflexive r] : Reflexive (SymmGen r) where
  refl x := SymmGen.incl (Reflexive.refl x)

instance {α} (r : α → α → Prop) [Reflexive r] : Reflexive (TransGen r) where
  refl x := TransGen.single (Reflexive.refl x)

/-! ## Irreflexivity -/

abbrev Irreflexive {α} (r : α → α → Prop) : Prop := Reflexive (¬r . .)

protected abbrev Irreflexive.irrefl {α} {r : α → α → Prop} [Irreflexive r] (x : α) := Reflexive.refl (r:=(¬r . .)) x

protected abbrev Irreflexive.irrfl {α} {r : α → α → Prop} [Irreflexive r] {x : α} := Irreflexive.irrefl (r:=r) x

theorem Irreflexive.ne_of {α} {r : α → α → Prop} [Irreflexive r] : {x y : α} → r x y → x ≠ y
| _, _, h, rfl => Irreflexive.irrfl h

instance (α) : Irreflexive (α:=α) (.≠.) := ⟨fun x h => h (Eq.refl x)⟩

/-! ## Symmetry -/

class HSymmetric (r : α → β → Prop) (s : β → α → Prop) : Prop where
  protected symm {x y} : r x y → s y x

class Symmetric (r : α → α → Prop) : Prop where
  protected symm {x y} : r y x → r x y

@[default_instance]
instance {α} (r : α → α → Prop) [Symmetric r] : HSymmetric r r := ⟨Symmetric.symm⟩

abbrev Asymmetric (r : α → α → Prop) := HSymmetric r (¬r . .)

protected def Asymmetric.asymm {α} {r : α → α → Prop} [Asymmetric r] {x y : α} : r x y → ¬r y x := HSymmetric.symm (r:=r) (s:=(¬r . .))

instance (α) : Symmetric (α:=α) (.=.) := ⟨Eq.symm⟩
instance (α) : Symmetric (α:=α) (.≠.) := ⟨Ne.symm⟩
instance (α) [Setoid α] : Symmetric (α:=α) (.≈.) := ⟨Setoid.symm⟩
instance (α) [Setoid α] : Symmetric (α:=α) Setoid.r := ⟨Setoid.symm⟩
instance (α β) : HSymmetric (α:=α) (β:=β) (.≅.) (.≅.) := ⟨HEq.symm⟩
instance (α) [LE α] : HSymmetric (α:=α) (.≤.) (.≥.) := ⟨id⟩
instance (α) [LE α] : HSymmetric (α:=α) (.≥.) (.≤.) := ⟨id⟩
instance (α) [LT α] : HSymmetric (α:=α) (.<.) (.>.) := ⟨id⟩
instance (α) [LT α] : HSymmetric (α:=α) (.>.) (.<.) := ⟨id⟩
instance : Symmetric (.↔.) := ⟨Iff.symm⟩

instance {α} (r : α → α → Prop) : Symmetric (SymmGen r) := ⟨SymmGen.symm⟩

instance {α} (r : α → α → Prop) : Symmetric (PartialEquivGen r) := ⟨PartialEquivGen.symm⟩

instance {α} (r : α → α → Prop) : Symmetric (EquivGen r) := ⟨EquivGen.symm⟩

instance {α} (r : α → α → Prop) [Symmetric r] : Symmetric (TransGen r) where
  symm := by
    intros x y hxy
    induction hxy with
    | single h =>
      apply TransGen.single
      exact Symmetric.symm h
    | tail _ h ih =>
      apply TransGen.trans
      exact TransGen.single (Symmetric.symm h)
      exact ih

/-! ## Antiymmetry -/

class HAntisymmetric {α} (r : α → α → Prop) (s : outParam <| α → α → Prop) : Prop where
  protected antisymm {x y} : r x y → r y x → s x y

class Antisymmetric {α} (r : α → α → Prop) : Prop where
  protected antisymm {x y} : r x y → r y x → x = y

@[default_instance]
instance {α} (r : α → α → Prop) [Antisymmetric r] : HAntisymmetric r Eq where
  antisymm := Antisymmetric.antisymm

instance : HAntisymmetric (.→.) (.↔.) := ⟨Iff.intro⟩

abbrev WeaklyConnex {α} (r : α → α → Prop) := Antisymmetric (fun x y => ¬r y x)

abbrev WeaklyConnex.connex {α} {r : α → α → Prop} [WeaklyConnex r] {x y} : ¬r y x → ¬r x y → x = y :=
  Antisymmetric.antisymm (r := fun x y => ¬r y x)

/-! ## Transitivity -/

class HTransitive {α β γ} (r : α → β → Prop) (s : β → γ → Prop) (t : outParam <| α → γ → Prop) : Prop where
  protected trans {x y z} : (left : r x y) → (right : s y z) → t x z

instance {α β γ} (r : α → β → Prop) (s : β → γ → Prop) (t : α → γ → Prop) [HTransitive r s t] : Trans r s t where
  trans := HTransitive.trans

class Transitive {α} (r : α → α → Prop) : Prop where
  protected trans {x y z} : (left : r x y) → (right : r y z) → r x z

@[default_instance]
instance {α} (r : α → α → Prop) [Transitive r] : HTransitive r r r := ⟨Transitive.trans⟩

instance (α) : Transitive (α:=α) (.=.) := ⟨Eq.trans⟩
instance (α β γ) : HTransitive (α:=α) (β:=β) (γ:=γ) (.≅.) (.≅.) (.≅.) := ⟨HEq.trans⟩
instance {α β} (r : α → β → Prop) : HTransitive (.=.) r r := ⟨fun he hr => Eq.substr he hr⟩
instance {α β} (r : α → β → Prop) : HTransitive r (.=.) r := ⟨fun hr he => Eq.subst he hr⟩
instance (α) [Setoid α] : Transitive (α:=α) (.≈.) := ⟨Setoid.trans⟩
instance (α) [Setoid α] : Transitive (α:=α) Setoid.r := ⟨Setoid.trans⟩
instance : Transitive (.→.) := ⟨fun h₁ h₂ h => h₂ (h₁ h)⟩
instance : Transitive (.↔.) := ⟨Iff.trans⟩

instance {α} (r : α → α → Prop) : Transitive (TransGen r) := ⟨TransGen.trans⟩

instance {α} (r : α → α → Prop) : Transitive (PartialEquivGen r) := ⟨PartialEquivGen.trans⟩

instance {α} (r : α → α → Prop) : Transitive (EquivGen r) := ⟨EquivGen.trans⟩

instance {α} (r : α → α → Prop) [Irreflexive r] [Transitive r] : Asymmetric r := ⟨fun hxy hyx => Irreflexive.irrfl (Transitive.trans hxy hyx)⟩

/-! ## Euclidean Property -/

class HEuclidean {α β γ} (r : α → β → Prop) (s : α → γ → Prop) (t : outParam <| β → γ → Prop) : Prop where
  protected eucl {x y z} : (left : r x y) → (right : s x z) → t y z

class Euclidean {α} (r : α → α → Prop) : Prop where
  protected eucl {x y z} : (left : r x y) → (right : r x z) → r y z

@[default_instance]
instance {α} (r : α → α → Prop) [Euclidean r] : HEuclidean r r r := ⟨Euclidean.eucl⟩

instance [Reflexive r] [Euclidean r] : Symmetric r where
  symm hxy := Euclidean.eucl hxy (Reflexive.refl _)

instance [Symmetric r] [Transitive r] : Euclidean r where
  eucl hxy hxz := Transitive.trans (Symmetric.symm hxy) hxz

def Euclidean.toSymmetric {α} (r : α → α → Prop) [Reflexive r] [Euclidean r] : Symmetric r where
  symm hxy := Euclidean.eucl hxy Reflexive.rfl

def Euclidean.toTransitive {α} (r : α → α → Prop) [Symmetric r] [Euclidean r] : Transitive r where
  trans hxy hyz := Euclidean.eucl (Symmetric.symm hxy) hyz

/-! ## Totality -/

class HTotal {α β} (r : α → β → Prop) (s : β → α → Prop) : Prop where
  protected total (x y) : r x y ∨ s y x

class Total {α} (r : α → α → Prop) : Prop where
  protected total (x y) : r x y ∨ r y x

@[default_instance]
instance {α} (r : α → α → Prop) [Total r] : HTotal r r := ⟨Total.total⟩

/-! ## Comparison Property -/

class HComparison {α} (r : α → α → Prop) (s : α → α → Prop) : Prop where
  protected compare {x y} : s x y → (z : α) → r x z ∨ r z y

class Comparison {α} (r : α → α → Prop) : Prop where
  protected compare {x y} : r x y → (z : α) → r x z ∨ r z y

@[default_instance]
instance {α} (r : α → α → Prop) [Comparison r] : HComparison r r := ⟨Comparison.compare⟩

def Transitive.toComparison {α} (r : α → α → Prop) [ComplementedRel r] [Transitive r] : Comparison fun x y => ¬r y x where
  compare := by
    intro x y nxy z
    by_cases r z x using Complemented with
    | .isFalse nxz =>
      left
      exact nxz
    | .isTrue hxz =>
      right
      intro hzy
      apply nxy
      exact Transitive.trans hzy hxz

instance Comparison.toTransitive {α} (r : α → α → Prop) [Comparison r] : Transitive fun x y => ¬r y x where
  trans := by
    intros x y z nxy nyz hxz
    cases Comparison.compare hxz y with
    | inl hyz => exact nyz hyz
    | inr hxy => exact nxy hxy

/-! ## Connexity -/

class HConnex {α} (r : α → α → Prop) (s : α → α → Prop) : Prop where
  protected connex {x y} : s x y → r x y ∨ r y x

class Connex {α} (r : α → α → Prop) : Prop where
  protected connex {x y} : x ≠ y → r x y ∨ r y x

@[default_instance]
instance {α} (r : α → α → Prop) [Connex r] : HConnex r (.≠.) := ⟨Connex.connex⟩

def Connex.toAntisymmetric {α} (r : α → α → Prop) [StableEq α] [Connex r] : Antisymmetric fun x y => ¬r y x where
  antisymm := by
    intro x y nxy nyx
    by_contradiction
    | assuming hne =>
      cases Connex.connex (r:=r) hne with
      | inl hyx => exact nyx hyx
      | inr hxy => exact nxy hxy

def Antisymmetric.toConnex {α} (r : α → α → Prop) [WeaklyComplementedRel r] [Antisymmetric r] : Connex fun x y => ¬r y x where
  connex := by
    intro x y hne
    apply and_deMorgan; intro ⟨hyx, hxy⟩
    apply hne
    exact Antisymmetric.antisymm hxy hyx

def Connex.toComparison {α} (r : α → α → Prop) [ComplementedEq α] [Connex r] [Transitive r] : Comparison r where
  compare := by
    intro x y hxy z
    by_cases x = z using Complemented with
    | .isTrue rfl => right; exact hxy
    | .isFalse hne =>
      match Connex.connex (r:=r) hne with
      | .inl hxz => left; exact hxz
      | .inr hzx => right; exact Transitive.trans hzx hxy
