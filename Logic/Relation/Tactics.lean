/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Logic.Relation.Classes

syntax "reflexivity" ("using" term:max)? : tactic
macro_rules
| `(tactic|reflexivity) => `(tactic|apply  Logic.Reflexive.rfl)
| `(tactic|reflexivity using $r:term) => `(tactic|apply  Logic.Reflexive.rfl (r:=$r))

syntax "irreflexivity" ("using" term:max)? : tactic
macro_rules
| `(tactic|irreflexivity) => `(tactic|apply  Logic.Irreflexive.irrfl)
| `(tactic|irreflexivity using $r:term) => `(tactic|apply  Logic.Irreflexive.irrfl (r:=$r))

syntax "symmetry" ("using" term:max ("," term:max)?)? : tactic
macro_rules
| `(tactic|symmetry) => `(tactic|first|apply  Logic.HSymmetric.symm _)
| `(tactic|symmetry using $r) => `(tactic|apply  Logic.Symmetric.symm (r:=$r) _)
| `(tactic|symmetry using $r, $s) => `(tactic|apply  Logic.HSymmetric.symm (r:=$r) (s:=$s) _)

syntax "antisymmetry" "using" term:max ("," term:max)? : tactic
macro_rules
| `(tactic|antisymmetry using $r) => `(tactic|apply  Logic.Antisymmetric.antisymm (r:=$r))
| `(tactic|antisymmetry using $r, $s) => `(tactic|apply  Logic.HAntisymmetric.antisymm (r:=$r) (s:=$s))

syntax "transitivity" term:max ("using" term:max ("," term:max)?)? : tactic
macro_rules
| `(tactic|transitivity $y) => `(tactic|apply  Logic.HTransitive.trans (y:=$y))
| `(tactic|transitivity $y using $r) => `(tactic|apply  Logic.Transitive.trans (r:=$r) (y:=$y))
| `(tactic|transitivity $y using $r, $s) => `(tactic|apply  Logic.HTransitive.trans (r:=$r) (s:=$s) (y:=$y))
