/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Logic.Proposition.Classes

syntax (name:=by_cases) "by_cases " term,* (&" using " ident)? &" with " Lean.Parser.Tactic.matchAlts : tactic

set_option hygiene false in macro_rules
| `(tactic| by_cases $ps,* with $alts) =>
  `(tactic| match $[inferInstanceAs (Decidable ($ps : Prop))],* with $alts:matchAlts)
| `(tactic| by_cases $ps:term,* using Complemented with $alts) =>
  `(tactic| match $[Logic.Complemented.byCases ($ps : Prop)],* with $alts:matchAlts)
| `(tactic| by_cases $ps:term,* using WeaklyComplemented with $alts) =>
  `(tactic| match $[Logic.WeaklyComplemented.byCases ($ps : Prop)],* with $alts:matchAlts)

syntax (name:=by_contradiction) "by_contradiction" withPosition(colGe ("|" &" assuming " ident "=>" tacticSeq)) : tactic
macro_rules
| `(tactic| by_contradiction | assuming $h:ident => $rest) =>
  `(tactic| apply Logic.Stable.by_contradiction _; intro $h:ident; ($rest))

syntax (name:=by_contrapositive) "by_contrapositive" withPosition(colGe ("|" &" assuming " ident "=>" tacticSeq)) : tactic
macro_rules
| `(tactic| by_contrapositive | assuming $h:ident => $rest) =>
  `(tactic| show Logic.Implies _ _; apply Logic.Stable.by_contrapositive; intro $h:ident; ($rest))

syntax (name:=by_no_counterexample) "by_no_counterexample" withPosition(colGe ("|" &" assuming " ident ident "=>" tacticSeq)) : tactic
macro_rules
| `(tactic| by_no_counterexample | assuming $x:ident $hx:ident => $rest) =>
  `(tactic| show Logic.Forall _ _; apply Logic.Stable.by_no_counterexample; intro ⟨$x:ident, $hx:ident⟩; ($rest))
