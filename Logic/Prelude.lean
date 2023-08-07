import Std

-- missing from Std
alias ⟨not_exists_of_forall_not, _⟩ := not_exists

register_simp_attr simp_cast

infix:50 " ≅ " => HEq

attribute [ext] Prod PProd Sigma PSigma
attribute [ext] Subtype.eq

macro "absurd " h:term : tactic => `(tactic| first | apply absurd _ $h | apply absurd $h)

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

