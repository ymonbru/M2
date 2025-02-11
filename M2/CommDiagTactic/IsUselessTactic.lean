import Lean


open Lean Meta Elab Tactic Term

/-- Almost stolen from metaprogramming exemples of siddhartha-gadgil

In the current context, check if evaluating the tactic tac is useful
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
