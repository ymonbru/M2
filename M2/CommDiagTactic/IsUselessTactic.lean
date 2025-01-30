import Lean


open Lean Meta Elab Tactic Term

/-- Almost stolen from metaprogramming exemples of siddhartha-gadgil

In the current context, evaluate the tactic first and then check if evaluating the tactic tac is useful, in particular if the goal is solved by the first tactic then tac is automaticaly useless.
-/
def IsUseless? (target: Expr)(tac: Syntax):
  TermElabM Bool :=
    withoutModifyingState do
    try
      let goal ← mkFreshExprMVar target
      let (goals, _) ←
        withoutErrToSorry do
        Elab.runTactic goal.mvarId! tac (← read) (← get)

      match goals with
        | [] => return false
        | [newGoal] => return goal.mvarId! == newGoal
        | _ => return false

    catch _ => -- the first tactic closes the goal
      return true

elab "is_useless" tac1:tacticSeq "after" tac2:tacticSeq  : tactic => withoutModifyingMCtx do
  let s0 ← saveState
  evalTactic tac2
  try
    let b ← IsUseless? (← getMainTarget) tac1
    restoreState s0
    if b then
      logInfo m!"Tactic is useless"
    else
      logInfo m!"Tactic does something"
  catch _ =>--the first tactic closes the goal
    restoreState s0
    logInfo m!"Tactic is useless but error"


variable (a b : Nat)
example (h : a = b): a + 1 = b + 1 := by

  is_useless (rw [h]) after skip

  rw [h]
