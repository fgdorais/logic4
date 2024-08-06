/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Batteries

infix:50 " ≅ " => HEq

open Lean Meta Elab

def Tactic.left (mvarId : MVarId) : MetaM (List MVarId) := do
  mvarId.withContext do
    mvarId.checkNotAssigned `left
    let target ← mvarId.getType'
    matchConstInduct target.getAppFn
      (fun _ => throwTacticEx `left mvarId "target is not an inductive datatype")
      fun ival us => do
        match ival.ctors with
        | [ctor,_] => mvarId.apply (mkConst ctor us)
        | _ => throwTacticEx `left mvarId "target is not an inductive datatype with two constructors"

elab "left" : tactic => Tactic.withMainContext do
  let gs ← Tactic.left (← Tactic.getMainGoal)
  Term.synthesizeSyntheticMVarsNoPostponing
  Tactic.replaceMainGoal gs

def Tactic.right (mvarId : MVarId) : MetaM (List MVarId) := do
  mvarId.withContext do
    mvarId.checkNotAssigned `right
    let target ← mvarId.getType'
    matchConstInduct target.getAppFn
      (fun _ => throwTacticEx `right mvarId "target is not an inductive datatype")
      fun ival us => do
        match ival.ctors with
        | [_,ctor] => mvarId.apply (mkConst ctor us)
        | _ => throwTacticEx `right mvarId "target is not an inductive datatype with two constructors"

elab "right" : tactic => Tactic.withMainContext do
  let gs ← Tactic.right (← Tactic.getMainGoal)
  Term.synthesizeSyntheticMVarsNoPostponing
  Tactic.replaceMainGoal gs

theorem Relation.TransGen.trans {r : α → α → Prop} (hl : TransGen r x y) (hr : TransGen r y z) :
    TransGen r x z := by
  induction hr with
  | single h => exact .tail hl h
  | tail _ h ih => exact .tail ih h
