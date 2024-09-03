/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Logic.Relation.Classes
import Logic.Relation.Tactics

namespace Logic
variable {α} (r : α → α → Prop)

abbrev coRel (x y) := ¬ r y x
abbrev reflRel (x y) := r x y ∨ x = y
abbrev asymRel (x y) := r x y ∧ coRel r x y
abbrev symmRel (x y) := r x y ∧ r y x

class abbrev Preorder : Prop := Reflexive r, Transitive r

abbrev inferPreorder [Reflexive r] [Transitive r] : Preorder r := .mk

class abbrev PartialOrder : Prop := Preorder r, Antisymmetric r

abbrev inferPartialOrder [Reflexive r] [Transitive r] [Antisymmetric r] : PartialOrder r := .mk

class abbrev TotalPreorder : Prop := Preorder r, Total r

abbrev inferTotalPreorder [Reflexive r] [Transitive r] [Total r] : TotalPreorder r := .mk

class abbrev TotalOrder : Prop := PartialOrder r, TotalPreorder r

abbrev inferTotalOrder [Reflexive r] [Transitive r] [Antisymmetric r] [Total r] : TotalOrder r := .mk

class abbrev Quasiorder : Prop := Transitive r, Reflexive (¬r . .)

abbrev inferQuasiorder [Transitive r] [Irreflexive r] : Quasiorder r := .mk

namespace Quasiorder
variable {r} [self : Quasiorder r]

protected theorem asymm {x y} : r x y → ¬ r y x := by
  intro _ _
  apply Irreflexive.irrefl (r:=r) x
  transitivity y <;> assumption

instance [self : Quasiorder r] : Asymmetric r := ⟨self.asymm⟩

end Quasiorder

class abbrev LinearQuasiorder : Prop := Quasiorder r, Comparison r

abbrev inferLinearQuasiorder [Transitive r] [Irreflexive r] [Comparison r] : LinearQuasiorder r := .mk

class abbrev LinearOrder : Prop := LinearQuasiorder r, Connex r

def inferLinearOrder [Transitive r] [Irreflexive r] [Comparison r] [Connex r] : LinearOrder r := .mk

namespace Preorder
variable {r} [self : Preorder r]

theorem co_irrefl (x) : ¬coRel r x x := by
  exact not_not_intro Reflexive.rfl

theorem co_compare [WeaklyComplementedRel r] {x y} : coRel r x y → ∀ z, coRel r x z ∨ coRel r z y := by
  intro cxy z
  rw [←Logic.nand_iff_not_or_not]
  intro ⟨hzx, hyz⟩
  absurd cxy
  exact Transitive.trans hyz hzx

theorem as_irrefl (x) : ¬asymRel r x x := by
  intro ⟨_, cxx⟩
  exact co_irrefl x cxx

theorem as_trans {x y z} : asymRel r x y → asymRel r y z → asymRel r x z := by
  intro ⟨hxy, cxy⟩ ⟨hyz, _⟩
  constructor
  · exact Transitive.trans hxy hyz
  · intro hzx
    absurd cxy
    exact Transitive.trans hyz hzx

instance : Quasiorder (asymRel r) where
  trans := as_trans
  refl := as_irrefl

end Preorder

namespace PartialOrder
variable {r} [self : PartialOrder r]

theorem co_connex [WeaklyComplementedRel r] {x y} : x ≠ y → coRel r x y ∨ coRel r y x := by
  intro hne
  rw [←nand_iff_not_or_not]
  intro ⟨hyx, hxy⟩
  absurd hne
  exact Antisymmetric.antisymm hxy hyx

end PartialOrder

namespace TotalPreorder
variable {r} [self : TotalPreorder r]

theorem coRel_iff_asymRel (x y) : coRel r x y ↔ asymRel r x y := by
  constructor
  · intro cxy
    constructor
    · cases Total.total (r:=r) x y with
      | inl hxy => exact hxy
      | inr hyx => absurd cxy; exact hyx
    · exact cxy
  · exact And.right

theorem co_irrefl (x) : ¬coRel r x x := by
  rw [coRel_iff_asymRel]
  reflexivity using (¬asymRel r . .)

theorem co_trans {x y z} : coRel r x y → coRel r y z → coRel r x z := by
  repeat rw [coRel_iff_asymRel]
  exact Preorder.as_trans

theorem as_compare [WeaklyComplementedRel r] {x y} : asymRel r x y → ∀ z, asymRel r x z ∨ asymRel r z y := by
  intro h z
  rw [←coRel_iff_asymRel] at h
  repeat rw [←coRel_iff_asymRel]
  exact Preorder.co_compare h z

instance : Quasiorder (coRel r) :=
  let _ : Transitive (coRel r) := ⟨co_trans⟩
  let _ : Irreflexive (coRel r) := ⟨co_irrefl⟩
  .mk

instance [WeaklyComplementedRel r] : LinearQuasiorder (coRel r) where
  toQuasiorder := inferInstance
  compare := Preorder.co_compare

instance [WeaklyComplementedRel r] : LinearQuasiorder (asymRel r) where
  toQuasiorder := inferInstance
  compare := TotalPreorder.as_compare

end TotalPreorder

namespace TotalOrder
variable {r} [self : TotalOrder r]

theorem coRel_iff_rel_and_ne (x y) : coRel r x y ↔ r x y ∧ x ≠ y := by
  constructor
  · intro cxy
    constructor
    · cases Total.total (r:=r) x y with
      | inl hxy => exact hxy
      | inr hyx => absurd cxy; exact hyx
    · intro | rfl => absurd cxy; exact Reflexive.rfl
  · intro ⟨hxy, hne⟩ hyx
    absurd hne
    exact Antisymmetric.antisymm hxy hyx

instance [WeaklyComplementedRel r] : LinearOrder (coRel r) where
  toLinearQuasiorder := inferInstance
  connex := PartialOrder.co_connex

end TotalOrder

namespace Quasiorder
variable {r} [self : Quasiorder r]

theorem co_refl (x) : coRel r x x := Irreflexive.irrfl

set_option linter.unusedSectionVars false in
theorem rc_refl (x) : reflRel r x x := by right; rfl

theorem rc_trans {x y z} : reflRel r x y → reflRel r y z → reflRel r x z := by
  intro hxy hyz
  match hxy, hyz with
  | Or.inr rfl, Or.inr rfl => right; rfl
  | Or.inr rfl, Or.inl hyz => left; exact hyz
  | Or.inl hxy, Or.inr rfl => left; exact hxy
  | Or.inl hxy, Or.inl hyz => left; exact Transitive.trans hxy hyz

theorem rc_antisymm {x y} : reflRel r x y → reflRel r y x → x = y := by
  intro hxy hyx
  match hxy, hyx with
  | Or.inr rfl, _ => rfl
  | _, Or.inr rfl => rfl
  | Or.inl hxy, Or.inl hyx =>
    absurd hxy
    exact Asymmetric.asymm hyx

instance : PartialOrder (reflRel r) where
  refl := Quasiorder.rc_refl
  trans := Quasiorder.rc_trans
  antisymm := Quasiorder.rc_antisymm

end Quasiorder

namespace LinearQuasiorder
variable {r} [self : LinearQuasiorder r]

theorem co_trans {x y z} : coRel r x y → coRel r y z → coRel r x z := by
  intro cxy cyz rzx
  cases Comparison.compare rzx y with
  | inl rzy => exact cyz rzy
  | inr ryx => exact cxy ryx

theorem co_total [ComplementedRel r] (x y) : coRel r x y ∨ coRel r y x := by
  by_cases r x y using Complemented with
  | .isTrue hxy => left; exact Asymmetric.asymm hxy
  | .isFalse nxy => right; exact nxy

instance : Preorder (coRel r) where
  refl := Quasiorder.co_refl
  trans := LinearQuasiorder.co_trans

instance [ComplementedRel r] : TotalPreorder (coRel r) where
  refl := Quasiorder.co_refl
  trans := LinearQuasiorder.co_trans
  total := LinearQuasiorder.co_total

end LinearQuasiorder

namespace LinearOrder
variable {r} [self : LinearOrder r]

theorem co_antisymm [StableEq α] {x y} : coRel r x y → coRel r y x → x = y := by
  intro cxy cyx
  by_contradiction
  | assuming hne =>
    cases Connex.connex (r:=r) hne with
    | inl hxy => absurd hxy; exact cyx
    | inr hyx => absurd hyx; exact cxy

theorem coRel_iff_reflRel [StableEq α] [ComplementedRel r] (x y) : coRel r x y ↔ reflRel r x y := by
  constructor
  · intro cxy
    by_cases r x y using Complemented with
    | .isTrue hxy => left; exact hxy
    | .isFalse cyx =>
      right
      by_contradiction
      | assuming hne =>
        cases Connex.connex (r:=r) hne with
        | inl hxy => absurd cyx; exact hxy
        | inr hyx => absurd cxy; exact hyx
  · intro
    | .inr rfl => exact Quasiorder.co_refl x
    | .inl hxy => exact Asymmetric.asymm hxy

theorem rc_total [ComplementedEq α] (x y) : reflRel r x y ∨ reflRel r y x := by
  by_cases x = y using Complemented with
  | .isTrue rfl => left; right; rfl
  | .isFalse hne =>
    cases Connex.connex (r:=r) hne with
    | inl hxy => left; left; exact hxy
    | inr hyx => right; left; exact hyx

instance [StableEq α] : PartialOrder (coRel r) where
  toPreorder := inferInstance
  antisymm := co_antisymm

instance [ComplementedRel r] [StableEq α] : TotalOrder (coRel r) where
  toPartialOrder := inferInstance
  total := LinearQuasiorder.co_total

instance [ComplementedEq α] : TotalOrder (reflRel r) where
  toPartialOrder := inferInstance
  total := LinearOrder.rc_total

end LinearOrder

end Logic
