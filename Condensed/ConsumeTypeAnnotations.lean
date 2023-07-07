import Lean
import Mathlib.Tactic.InferParam


open Lean Elab Tactic
elab "consume" : tactic => do
  withMainContext do
    let mvarIds ← getMainGoal
    mvarIds.setType (← mvarIds.getType).consumeTypeAnnotations

macro "constructor" : tactic =>
  `(tactic| constructor <;> ((try infer_param) <;> consume))


structure a where
  l : Nat := by fail
  k : Nat := by exact 2

example : a := by
  constructor
  sorry
