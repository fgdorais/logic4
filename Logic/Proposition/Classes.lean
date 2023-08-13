import Logic.Basic

namespace Logic

/-! ## Stable Propositions -/

/-- Class of stable propositions -/
class Stable (a : Prop) : Prop where intro :: elim : ¬¬a → a

/-- Class abbreviation for stable predicates -/
abbrev StablePred {α} (p : α → Prop) := (x : α) → Stable (p x)

/-- Class abbreviation for stable relations -/
abbrev StableRel {α β} (r : α → β → Prop) := (x : α) → (y : β) → Stable (r x y)

/-- Class abbreviation for stable equality -/
abbrev StableEq (α) := StableRel (@Eq α)

/-- Find a `Stable` instance for a given proposition -/
def inferStable (a : Prop) [inst : Stable a] := inst

/-- Double Negation Elimination (DNE) -/
theorem Stable.dne (a : Prop) [Stable a] : ¬¬a → a := Stable.elim

/-- Proof by contradiction for a stable proposition -/
theorem Stable.by_contradiction [Stable a] : ¬¬a → a := Stable.elim

/-- Proof by contrapositive for a stable implication -/
def Stable.by_contrapositive [Stable b] : (¬b → ¬a) → (a → b) :=
  fun h ha => Stable.by_contradiction fun hnb => h hnb ha

/-- Proof by no counterexamples for a stable universal -/
def Stable.by_no_counterexample {a : α → Prop} [StablePred a] : ¬(∃ x, ¬a x) → (∀ x, a x) :=
  fun h x => Stable.by_contradiction fun hx => h ⟨x, hx⟩

/-- Pierces's law for stable propositions -/
theorem Stable.pierce (a b : Prop) [Stable a] : ((a → b) → a) → a :=
  fun h => by_contradiction fun na => na <| h fun ha => absurd ha na

set_option checkBinderAnnotations false in
/-- Class for lists of stable propositions -/
class inductive StableList : List Prop → Prop
| instNil : StableList []
| instCons (a as) : [Stable a] → [StableList as] → StableList (a :: as)
attribute [instance] StableList.instNil StableList.instCons

/-- Head of a `StableList` -/
def StableList.head (a as) : [StableList (a :: as)] → Stable a
| instCons .. => inferInstance

/-- Tail of a `StableList` -/
def StableList.tail (a as) : [StableList (a :: as)] → StableList as
| instCons .. => inferInstance

instance StableList.instMap (a : α → Prop) [StablePred a] : (xs : List α) → StableList (xs.map a)
| [] => instNil
| _::xs => let _ := instMap a xs; instCons ..

/-! ## Complemented Propositions -/

/-- Class for complemented propositions -/
class Complemented (a : Prop) : Prop where intro :: elim : a ∨ ¬a

/-- True propositions are complemented -/
def Complemented.isTrue (h : a) : Complemented a := intro (.inl h)

/-- False propositions are complemented -/
def Complemented.isFalse (h : ¬a) : Complemented a := intro (.inr h)

/-- Find a `Complemented` instance for a given proposition -/
def inferComplemented (a : Prop) [inst : Complemented a] := inst

/-- Law of Excluded Middle (EM) -/
theorem Complemented.em (a : Prop) [Complemented a] : a ∨ ¬a := Complemented.elim

/-- Inductive cases view for `Complemented` -/
inductive Complemented.Cases (a : Prop) : Prop
| isTrue : a → Cases a
| isFalse : ¬a → Cases a

/-- Cases view of a complemented proposition -/
def Complemented.byCases (a : Prop) [Complemented a] : Cases a :=
  match em a with
  | .inl h => .isTrue h
  | .inr h => .isFalse h

/-- Proof by cases for complemented propositions -/
def Complemented.by_cases (a : Prop) [Complemented a] {motive : Prop} (isTrue : a → motive) (isFalse : ¬a → motive) : motive :=
  match byCases a with
  | .isTrue h => isTrue h
  | .isFalse h => isFalse h

/-- Class abbreviation for complemented predicates -/
abbrev ComplementedPred (p : α → Prop) := (x : α) → Complemented (p x)

/-- Class abbreviation for complemented relations -/
abbrev ComplementedRel (r : α → β → Prop) := (x : α) → (y : β) → Complemented (r x y)

/-- Class abbreviation for complemented equality -/
abbrev ComplementedEq (α) := ComplementedRel (@Eq α)

set_option checkBinderAnnotations false in
/-- Class for lists of complemented propositions -/
class inductive ComplementedList : List Prop → Prop
| instNil : ComplementedList []
| instCons (a as) : [Complemented a] → [ComplementedList as] → ComplementedList (a :: as)
attribute [instance] ComplementedList.instNil ComplementedList.instCons

/-- Head of a `ComplementedList` -/
protected def ComplementedList.head (a as) : [ComplementedList (a :: as)] → Complemented a
| instCons .. => inferInstance

/-- Tail of a `ComplementedList` -/
protected def ComplementedList.tail (a as) : [ComplementedList (a :: as)] → ComplementedList as
| instCons .. => inferInstance

instance ComplementedList.instMap (a : α → Prop) [ComplementedPred a] : (xs : List α) → ComplementedList (xs.map a)
| [] => instNil
| _::xs => let _ := instMap a xs; instCons ..

/-! ## Weakly Complemented Propositions -/

/-- Class abbreviation for weakly complemented propositions -/
abbrev WeaklyComplemented (a : Prop) : Prop := Complemented (¬a)

/-- Find a `WeaklyComplemented` instance for a given proposition -/
def inferWeaklyComplemented (a : Prop) [inst : WeaklyComplemented a] := inst

/-- Constructor abbreviation for `WeaklyComplemented` -/
abbrev WeaklyComplemented.intro (h : ¬a ∨ ¬¬a) : WeaklyComplemented a := Complemented.intro h

/-- False propositions are weakly complemented -/
def WeaklyComplemented.isFalse (h : ¬a) : WeaklyComplemented a := intro (.inl h)

/-- Irrefutable propositions are weakly complemented -/
def WeaklyComplemented.isIrrefutable (h : ¬¬a) : WeaklyComplemented a := intro (.inr h)

/-- Weak Excluded Middle (WEM) -/
theorem WeaklyComplemented.wem (a : Prop) [WeaklyComplemented a] : ¬a ∨ ¬¬a :=
  Complemented.elim

/-- Inductive cases view for `WeaklyComplemented` -/
inductive WeaklyComplemented.Cases (a : Prop) : Prop
| isFalse : ¬a → Cases a
| isIrrefutable : ¬¬a → Cases a

/-- Cases view of a weakly complemented proposition -/
def WeaklyComplemented.byCases (a : Prop) [WeaklyComplemented a] : Cases a :=
  match wem a with
  | .inl h => .isFalse h
  | .inr h => .isIrrefutable h

/-- Proof by cases for weakly complemented propositions -/
def WeaklyComplemented.by_cases (a : Prop) [WeaklyComplemented a] {motive : Prop} (isFalse : ¬a → motive) (isIrrefutable : ¬¬a → motive) : motive :=
  match byCases a with
  | .isFalse h => isFalse h
  | .isIrrefutable h => isIrrefutable h

/-- Class abbreviation for weakly complemented predicates -/
abbrev WeaklyComplementedPred {α} (p : α → Prop) := (x : α) → WeaklyComplemented (p x)

/-- Class abbreviation for weakly complemented relations -/
abbrev WeaklyComplementedRel {α β} (r : α → β → Prop) := (x : α) → (y : β) → WeaklyComplemented (r x y)

/-- Class abbreviation for weakly complemented equality -/
abbrev WeaklyComplementedEq (α) := WeaklyComplementedRel (@Eq α)

set_option checkBinderAnnotations false in
/-- Class for lists of weakly complemented propositions -/
class inductive WeaklyComplementedList : List Prop → Prop
| instNil : WeaklyComplementedList []
| instCons (a as) : [WeaklyComplemented a] → [WeaklyComplementedList as] → WeaklyComplementedList (a :: as)
attribute [instance] WeaklyComplementedList.instNil WeaklyComplementedList.instCons

/-- Head of a `WeaklyComplementedList` -/
protected def WeaklyComplementedList.head (a as) : [WeaklyComplementedList (a :: as)] → WeaklyComplemented a
| instCons .. => inferInstance

/-- Tail of a `WeaklyComplementedList` -/
protected def WeaklyComplementedList.tail (a as) : [WeaklyComplementedList (a :: as)] → WeaklyComplementedList as
| instCons .. => inferInstance

instance WeaklyComplementedList.instMap (a : α → Prop) [WeaklyComplementedPred a] : (xs : List α) → WeaklyComplementedList (xs.map a)
| [] => instNil
| _::xs => let _ := instMap a xs; instCons ..

/-! ## Instances -/

/- Decidable propositions are complemented -/
instance (a) [Decidable a] : Complemented a := ⟨Decidable.em a⟩

namespace Stable

/- Complemented propositions are stable -/
instance (a) [Complemented a] : Stable a :=
  match Complemented.byCases a with
  | .isTrue h => intro (fun _ => h)
  | .isFalse h => intro (absurd h)

/- Complemented propositions are weakly complemented -/
instance (a b) [Stable a] [Stable b] : Stable (a ∧ b) :=
  intro fun hnn =>
    let ha : a := by_contradiction fun hna => hnn fun h => hna h.left
    let hb : b := by_contradiction fun hnb => hnn fun h => hnb h.right
    ⟨ha, hb⟩

instance (a b) [Stable b] : Stable (a → b) :=
  intro fun hnn ha => by_contradiction fun hnb => hnn fun h => hnb (h ha)

instance (a) : Stable (¬a) := inferStable (a → False)

instance (a : α → Prop) [StablePred a] : Stable (∀ x, a x) :=
  intro fun hnn x => by_contradiction fun hnax => hnn fun h => hnax (h x)

instance (β : α → Sort _) [(x : α) → StableEq (β x)] : StableEq ((x : α) → β x) :=
  fun _ _ => intro fun hnn => funext fun _ => by_contradiction fun hn => hnn fun | rfl => hn rfl

instance (α β) [StableEq β] : StableEq (α → β) := inferInstance

instance (a b) [Stable a] [Complemented b] : Stable (a ∨ b) :=
  match Complemented.byCases b with
  | .isTrue hb => intro fun _ => .inr hb
  | .isFalse nb => intro fun hnn => .inl <| by_contradiction fun na => hnn fun | .inl ha => na ha | .inr hb => nb hb

instance (a b) [Stable b] [Complemented a] : Stable (a ∨ b) :=
  match Complemented.byCases a with
  | .isTrue ha => intro fun _ => .inl ha
  | .isFalse na => intro fun hnn => .inr <| by_contradiction fun nb => hnn fun | .inl ha => na ha | .inr hb => nb hb

instance instAll : (as : List Prop) → [StableList as] → Stable (All as)
| [], _ => all_nil_eq ▸ inferStable True
| a::as, StableList.instCons .. => let _ := instAll as; all_cons_eq .. ▸ inferStable (a ∧ All as)

end Stable

namespace Complemented

/- Weakly complemented stable propositions are complemented -/
instance (a) [Stable a] [WeaklyComplemented a] : Complemented a :=
  match WeaklyComplemented.byCases a with
  | .isFalse h => .isFalse h
  | .isIrrefutable h => .isTrue (Stable.by_contradiction h)

instance (a b) [Complemented a] [Complemented b] : Complemented (a ∨ b) :=
  match Complemented.byCases a, Complemented.byCases b with
  | .isTrue ha, _ => isTrue (.inl ha)
  | _, .isTrue hb => isTrue (.inr hb)
  | .isFalse na, .isFalse nb => isFalse fun | .inl ha => na ha | .inr hb => nb hb

instance [Complemented a] [Complemented b] : Complemented (a ∧ b) :=
  match Complemented.byCases a, Complemented.byCases b with
  | .isFalse na, _ => isFalse fun h => na (And.left h)
  | _, .isFalse nb => isFalse fun h => nb (And.right h)
  | .isTrue ha, .isTrue hb => isTrue (And.intro ha hb)

instance (a) [Complemented a] : Complemented (¬a) :=
  match Complemented.byCases a with
  | .isTrue h => .isFalse (not_not_intro h)
  | .isFalse h => .isTrue h

instance [WeaklyComplemented a] [Complemented b] : Complemented (a → b) :=
  match WeaklyComplemented.byCases a, Complemented.byCases b with
| .isFalse na, _ => isTrue fun ha => absurd ha na
| _, .isTrue hb => isTrue fun _ => hb
| .isIrrefutable ha, .isFalse nb => isFalse fun h => ha fun ha => absurd (h ha) nb

instance [Complemented a] [Complemented b] : Complemented (a ↔ b) :=
  propext (iff_iff_implies_and_implies ..) ▸ inferComplemented ((a → b) ∧ (b → a))

instance instAll : (as : List Prop) → [ComplementedList as] → Complemented (All as)
| [], _ => all_nil_eq ▸ inferComplemented True
| a::as, ComplementedList.instCons .. => let _ := instAll as; all_cons_eq .. ▸ inferComplemented (a ∧ All as)

instance instAny : (as : List Prop) → [ComplementedList as] → Complemented (Any as)
| [], _ => any_nil_eq ▸ inferComplemented False
| a::as, ComplementedList.instCons .. => let _ := instAny as; any_cons_eq .. ▸ inferComplemented (a ∨ Any as)

end Complemented

namespace WeaklyComplemented

/- Complemented propositions are weakly complemented -/
instance (a) [Complemented a] : WeaklyComplemented a := inferInstance

instance (a b) [WeaklyComplemented a] [WeaklyComplemented b] : WeaklyComplemented (a ∨ b) :=
  match WeaklyComplemented.byCases a, WeaklyComplemented.byCases b with
  | .isIrrefutable ha, _ => isIrrefutable fun h => ha fun ha => h (Or.inl ha)
  | _, .isIrrefutable hb => isIrrefutable fun h => hb fun hb => h (Or.inr hb)
  | .isFalse ha, .isFalse hb => isFalse fun | Or.inl h => ha h | Or.inr h => hb h

instance (a b) [WeaklyComplemented a] [WeaklyComplemented b] : WeaklyComplemented (a ∧ b) :=
  match WeaklyComplemented.byCases a, WeaklyComplemented.byCases b with
  | .isFalse ha, _ => isFalse fun ⟨h,_⟩  => ha h
  | _, .isFalse hb => isFalse fun ⟨_,h⟩  => hb h
  | .isIrrefutable ha, .isIrrefutable hb => isIrrefutable fun h => ha fun ha => hb fun hb => h (And.intro ha hb)

instance (a b) [WeaklyComplemented a] [WeaklyComplemented b] : WeaklyComplemented (a → b) :=
  match WeaklyComplemented.byCases a, WeaklyComplemented.byCases b with
  | .isFalse ha, _ => isIrrefutable fun h => h fun h => absurd h ha
  | _, .isIrrefutable hb => isIrrefutable fun h => hb fun hb => h fun _ => hb
  | .isIrrefutable ha, .isFalse hb => isFalse fun h => ha fun ha => hb (h ha)

instance (a b) [WeaklyComplemented a] [WeaklyComplemented b] : WeaklyComplemented (a ↔ b) :=
  propext (iff_iff_implies_and_implies ..) ▸ inferWeaklyComplemented ((a → b) ∧ (b → a))

instance instAll : (as : List Prop) → [WeaklyComplementedList as] → WeaklyComplemented (All as)
| [], _ => all_nil_eq ▸ inferWeaklyComplemented True
| a::as, WeaklyComplementedList.instCons .. => let _ := instAll as; all_cons_eq .. ▸ inferWeaklyComplemented (a ∧ All as)

instance instAny : (as : List Prop) → [WeaklyComplementedList as] → WeaklyComplemented (Any as)
| [], _ => any_nil_eq ▸ inferWeaklyComplemented False
| a::as, WeaklyComplementedList.instCons .. => let _ := instAny as; any_cons_eq .. ▸ inferWeaklyComplemented (a ∨ Any as)

end WeaklyComplemented
