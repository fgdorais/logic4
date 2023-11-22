/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Logic.Proposition.Classes
import Logic.Proposition.Lemmas
import Logic.Proposition.Tactics

namespace Logic

/-! ## Omniscient Types -/

/-- Class for omniscient types -/
class Omniscient (α : Type _) : Prop where intro ::
  elim (a : α → Prop) [ComplementedPred a] : (∃ x, a x) ∨ ¬(∃ x, a x)

instance (a : α → Prop) [ComplementedPred a] [Omniscient α] : Complemented (∃ x, a x) where
  elim := Omniscient.elim a

/-- Transfer weak omniscience to equivalent type -/
def Omniscient.ofEquiv {α β} (e : Equiv α β) [Omniscient α] : Omniscient β where
  elim a _ := by
    by_cases ∃ x, a (e.fwd x) using Complemented with
    | .isTrue ⟨x, _⟩ => left; exists e.fwd x
    | .isFalse h => right; intro ⟨y, _⟩; apply h; exists e.rev y; rwa [e.fwd_rev]

instance : Omniscient Empty where
  elim _ _ := by right; intro ⟨_,_⟩; contradiction

instance : Omniscient Unit where
  elim a _ := by
    by_cases a () using Complemented with
    | .isTrue _ => left; exists ()
    | .isFalse _ => right; intro ⟨_,_⟩; contradiction

instance : Omniscient Bool where
  elim a _ := by
    by_cases a true, a false using Complemented with
    | .isTrue _, _ => left; exists true
    | _, .isTrue _ => left; exists false
    | .isFalse _, .isFalse _ => right; intro
      | ⟨true, _⟩ => contradiction
      | ⟨false, _⟩ => contradiction

instance : Omniscient Ordering where
  elim a _ := by
    by_cases a .lt, a .eq, a .gt using Complemented with
    | .isTrue _, _, _ => left; exists .lt
    | _, .isTrue _, _ => left; exists .eq
    | _, _, .isTrue _ => left; exists .gt
    | .isFalse _, .isFalse _, .isFalse _ => right; intro
      | ⟨.lt, _⟩ => contradiction
      | ⟨.eq, _⟩ => contradiction
      | ⟨.gt, _⟩ => contradiction

instance instOmniscientFin : (n : Nat) → Omniscient (Fin n)
  | 0 => .intro fun a _ => .inr fun .
  | n+1 => .intro fun a _ => by
    have _ : Omniscient (Fin n) := instOmniscientFin n
    by_cases a 0, ∃ i, a (.succ i) using Complemented with
    | .isTrue _, _ => left; exists 0
    | _, .isTrue ⟨i, _⟩ => left; exists .succ i
    | .isFalse _, .isFalse h => right; intro
      | ⟨⟨0, _⟩, _⟩ => contradiction
      | ⟨⟨i+1, hi⟩, _⟩ => absurd h; exists ⟨i, Nat.lt_of_succ_lt_succ hi⟩

instance (α) [Omniscient α] : Omniscient (Option α) where
  elim a _ := by
    by_cases a none, ∃ x, a (some x) using Complemented with
    | .isTrue _, _ => left; exists none
    | _, .isTrue ⟨x, _⟩ => left; exists some x
    | .isFalse _, .isFalse h => right; intro
      | ⟨none, _⟩ => contradiction
      | ⟨some x, _⟩ => absurd h; exists x

instance (α β) [Omniscient α] [Omniscient β] : Omniscient (Sum α β) where
  elim a _ := by
    by_cases ∃ x, a (.inl x), ∃ y, a (.inr y) using Complemented with
    | .isTrue ⟨x, _⟩, _ => left; exists .inl x
    | _, .isTrue ⟨y, _⟩ => left; exists .inr y
    | .isFalse ha, .isFalse hb => right; intro
      | ⟨.inl x, _⟩ => absurd ha; exists x
      | ⟨.inr y, _⟩ => absurd hb; exists y

instance (α β) [Omniscient α] [Omniscient β] : Omniscient (α × β) where
  elim a _ := by
    by_cases ∃ x y, a (x, y) using Complemented with
    | .isTrue ⟨x, y, _⟩ => left; exists (x, y)
    | .isFalse h => right; intro
      | ⟨(x, y), _⟩ => absurd h; exists x, y

instance (β : α → Type _) [Omniscient α] [(x : α) → Omniscient (β x)] : Omniscient ((x : α) × β x) where
  elim a _ := by
    by_cases ∃ x y, a ⟨x, y⟩ using Complemented with
    | .isTrue ⟨x, y, _⟩ => left; exists ⟨x, y⟩
    | .isFalse h => right; intro
      | ⟨⟨x, y⟩, _⟩ => absurd h; exists x, y

/-! ## Weakly Omniscient Types -/

/-- Class for weakly omniscient types -/
class WeaklyOmniscient (α : Type _) : Prop where intro ::
  elim (a : α → Prop) [ComplementedPred a] : (∀ x, a x) ∨ ¬(∀ x, a x)

instance (a : α → Prop) [ComplementedPred a] [WeaklyOmniscient α] : Complemented (∀ x, a x) where
  elim := WeaklyOmniscient.elim a

instance (a : α → Prop) [ComplementedPred a] [WeaklyOmniscient α] : WeaklyComplemented (∃ x, a x) where
  elim := match WeaklyOmniscient.elim (¬a .) with
    | .inl h => .inl (not_exists.2 h)
    | .inr h => .inr fun h' => h (not_exists.1 h')

/-- Transfer weak omniscience to equivalent type -/
def WeaklyOmniscient.ofEquiv {α β} (e : Equiv α β) [WeaklyOmniscient α] : WeaklyOmniscient β where
  elim a _ := by
    by_cases ∀ x, a (e.fwd x) using Complemented with
    | .isTrue h => left; intro y; rw [←e.fwd_rev y]; exact h ..
    | .isFalse h => right; intro hb; absurd h; intro x; rw [←e.rev_fwd x]; exact hb ..

/-- Omniscient types are weakly omniscient -/
instance (α) [Omniscient α] : WeaklyOmniscient α where
  elim a _ := by
    by_cases (∃ x, ¬a x) using Complemented with
    | .isTrue ⟨x, hx⟩ => right; intro h; absurd h x; exact hx
    | .isFalse h => left; intro x; by_contradiction | assuming hx => apply h; exists x

instance (α) [WeaklyOmniscient α] : WeaklyOmniscient (Option α) where
  elim a _ := by
    by_cases a none, ∀ x, a (some x) using Complemented with
    | .isTrue hn, .isTrue hs => left; intro
      | none => exact hn
      | some _ => exact hs ..
    | .isFalse hn, _ => right; intro h; absurd h none; exact hn
    | _, .isFalse hs => right; intro h; absurd hs; intro x; exact h ..

instance (α β) [WeaklyOmniscient α] [WeaklyOmniscient β] : WeaklyOmniscient (Sum α β) where
  elim a _ := by
    by_cases ∀ x, a (.inl x), ∀ y, a (.inr y) using Complemented with
    | .isTrue hl, .isTrue hr => left; intro
      | .inl _ => exact hl ..
      | .inr _ => exact hr ..
    | .isFalse hl, _ => right; intro h; absurd hl; intro; exact h ..
    | _, .isFalse hr => right; intro h; absurd hr; intro; exact h ..

instance (α β) [WeaklyOmniscient α] [WeaklyOmniscient β] : WeaklyOmniscient (α × β) where
  elim a _ := by
    by_cases ∀ x y, a (x, y) using Complemented with
    | .isTrue h => left; intro ⟨_,_⟩; exact h ..
    | .isFalse h => right; intro hp; absurd h; intros; exact hp ..

instance (β : α → Type _) [WeaklyOmniscient α] [(x : α) → WeaklyOmniscient (β x)] : WeaklyOmniscient ((x : α) × β x) where
  elim a _ := by
    by_cases ∀ x y, a ⟨x, y⟩ using Complemented with
    | .isTrue h => left; intro ⟨_,_⟩; exact h ..
    | .isFalse h => right; intro hp; absurd h; intros; exact hp ..

/-! ## Markovian Types -/

/-- Class for Markovian types -/
class Markovian (α : Type _) : Prop where intro ::
  elim (a : α → Prop) [ComplementedPred a] : ¬¬(∃ x, a x) → (∃ x, a x)

instance (a : α → Prop) [Markovian α] [ComplementedPred a] : Stable (∃ x, a x) :=
  Stable.intro (Markovian.elim a)

/-- Transfer Markov property to equivalent type -/
def Markovian.ofEquiv {α β} (e : Equiv α β) [Markovian α] : Markovian β where
  elim a _ h := by
    have : ¬¬∃ x, a (e.fwd x) := by
      intro hx
      apply h
      intro ⟨y, hy⟩
      apply hx
      exists (e.rev y)
      rwa [e.fwd_rev]
    match Markovian.elim _ this with
    | ⟨x, _⟩ => exists e.fwd x

theorem not_forall {a : α → Prop} [Markovian α] [ComplementedPred a] : ¬(∀ x, a x) ↔ (∃ x, ¬a x) := by
  constructor
  · intro h
    by_contradiction
    | assuming h' =>
      apply h
      intro x
      by_contradiction
      | assuming hx =>
        apply h'
        exists x
  · intro ⟨x, hx⟩
    intro h
    apply hx
    exact h x

/-- Omniscient types are Markovian -/
instance [Omniscient α] : Markovian α where
  elim a _ h := by
    match Omniscient.elim a with
    | .inl h => exact h
    | .inr _ => absurd h; assumption

instance (α) [Markovian α] : Markovian (Option α) where
  elim a _ h := by
    by_cases a none using Complemented with
    | .isTrue _ => exists none
    | .isFalse _ =>
      have : ¬¬∃ x, a (some x) := by
        intro hs
        apply h
        intro
        | ⟨none, _⟩ => contradiction
        | ⟨some x, _⟩ => absurd hs; exists x
      match Markovian.elim _ this with
      | ⟨x, _⟩ => exists x

instance (α β) [Markovian α] [Omniscient β] : Markovian (Sum α β) where
  elim a _ h := by
    by_cases ∃ y, a (.inr y) using Complemented with
    | .isTrue ⟨y, _⟩  => exists .inr y
    | .isFalse hy =>
      have : ¬¬∃ x, a (.inl x) := by
        intro hx
        apply h
        intro
        | ⟨.inl x, _⟩ => absurd hx; exists x
        | ⟨.inr y, _⟩ => absurd hy; exists y
      match Markovian.elim _ this with
      | ⟨x, _⟩ => exists .inl x

instance (α β) [Omniscient α] [Markovian β] : Markovian (Sum α β) where
  elim a _ h := by
    by_cases ∃ x, a (.inl x) using Complemented with
    | .isTrue ⟨x, _⟩  => exists .inl x
    | .isFalse hx =>
      have : ¬¬∃ y, a (.inr y) := by
        intro hy
        apply h
        intro
        | ⟨.inl x, _⟩ => absurd hx; exists x
        | ⟨.inr y, _⟩ => absurd hy; exists y
      match Markovian.elim _ this with
      | ⟨y, _⟩ => exists .inr y

instance (β : α → Type _) [Markovian α] [(x : α) → Omniscient (β x)] : Markovian ((x : α) × β x) where
  elim a _ h := by
    have : ¬¬∃ x, ∃ (y : β x), a ⟨x, y⟩ := by
      intro h'
      apply h
      intro ⟨⟨x, y⟩, _⟩
      apply h'
      exists x, y
    match Markovian.elim _ this with
    | ⟨x, ⟨y, h⟩⟩ => exists ⟨x, y⟩

/-! ## Expermiental -/

/-- Class for Disjunctive type pairs -/
class Disjunctive (α β : Type _) : Prop where intro ::
  elim (a : α → Prop) (b : β → Prop) [ComplementedPred a] [ComplementedPred b] :
    ¬¬(∀ x y, a x ∨ b y) → ¬¬(∀ x, a x) ∨ ¬¬(∀ y, b y)
