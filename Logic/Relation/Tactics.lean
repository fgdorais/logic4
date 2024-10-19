/-
Copyright © 2023-2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Logic.Relation.Classes

syntax "reflexivity" ("using" term:max)? : tactic
macro_rules
| `(tactic| reflexivity) => `(tactic| apply Relation.Reflexive.rfl)
| `(tactic| reflexivity using $r:term) => `(tactic| apply Relation.Reflexive.rfl (r:=$r))

syntax "irreflexivity" ("using" term:max)? : tactic
macro_rules
| `(tactic| irreflexivity) => `(tactic| apply Relation.Irreflexive.irrfl)
| `(tactic| irreflexivity using $r:term) => `(tactic| apply Relation.Irreflexive.irrfl (r:=$r))

syntax "symmetry" ("using" term:max ("," term:max)?)? : tactic
macro_rules
| `(tactic| symmetry) => `(tactic| apply Relation.HSymmetric.symm _)
| `(tactic| symmetry using $r) => `(tactic| apply Relation.Symmetric.symm (r:=$r) _)
| `(tactic| symmetry using $r, $s) => `(tactic| apply Relation.HSymmetric.symm (r:=$r) (s:=$s) _)

syntax "antisymmetry" "using" term:max ("," term:max)? : tactic
macro_rules
| `(tactic| antisymmetry using $r) => `(tactic| apply Relation.Antisymmetric.antisymm (r:=$r))
| `(tactic| antisymmetry using $r, $s) => `(tactic| apply Relation.HAntisymmetric.antisymm (r:=$r) (s:=$s))
