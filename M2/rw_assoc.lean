import Lean
import Mathlib.Tactic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Tactic.CategoryTheory.Slice

open CategoryTheory Lean Meta Elab Tactic

/--Compute the length of a sequence of composition-/
partial def compLength (e : Expr) : MetaM Nat := do
  if e.isAppOf ``CategoryStruct.comp then
    return (← compLength (e.getArg! 5)) + (← compLength (e.getArg! 6)) + 1
  else
    return 0
/--Compute the maximal length of an equality of sequence of composition-/
def eqLength (e : Expr) : MetaM Nat := do
  let e ← whnf e
  if e.isAppOf ``Eq then
    return max (← compLength (e.getArg! 1)) (← compLength (e.getArg! 2))
  else
    return 0


/-- take the maximal length of composition in the goal and try to rewrite it at every position possible.
  It takes into account that the hypothesis could be in the other direction and on the left or the right of the equality
  I don't use the right hand side in my algo

TODO: try the variang with the direct computation of the position of the slice-/
elab "rw_assoc" h:term : tactic => withMainContext do
  let n ← eqLength (← getMainTarget)
  let s0 ← saveState
  for j in [0:n+1] do
    let s ← saveState
    let jLit := Syntax.mkNumLit <| toString j
    let jLitSucc := Syntax.mkNumLit <| toString (j+1)
    try
      evalTactic $ ← `(tactic |  slice_lhs $jLit $jLitSucc => first | rw [ ($h)] | rw [← ($h)])
      return
    catch _ =>
      restoreState s

    try
      evalTactic $ ← `(tactic |  slice_rhs $jLit $jLitSucc => first | rw [ ($h)] | rw [←  ($h)])
      return
    catch _ =>
      restoreState s
  restoreState s0
  throwError m!"rw_assoc did not find {h} in the first {n} terms of the composition"
