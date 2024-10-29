import Lean
import Mathlib.Tactic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Tactic.CategoryTheory.Slice

open CategoryTheory Lean Meta Elab Tactic

partial def compLength (e : Expr) : MetaM Nat := do
  if e.isAppOf ``CategoryStruct.comp then
    return (← compLength (e.getArg! 5)) + (← compLength (e.getArg! 6)) + 1
  else
    return 0

def eqLength (e : Expr) : MetaM Nat := do
  let e ← whnf e
  if e.isAppOf ``Eq then
    return max (← compLength (e.getArg! 1)) (← compLength (e.getArg! 2))
  else
    return 0

macro "slice_lhs_aux" a:num "et " b:num "avec" h:term : tactic =>
  `(tactic| slice_lhs $a $b => rw [ ($h)])

macro "slice_rhs_aux" a:num "et " b:num "avec" h:term : tactic =>
  `(tactic| slice_rhs $a $b => rw [ ($h)])


/-TODO: try the variang with the direct computation of the position of the slice-/
elab "rw_assoc" h:term : tactic => withMainContext do
  let n ← eqLength (← getMainTarget)
  let s0 ← saveState
  for j in [0:n+1] do
    let s ← saveState
    let jLit := Syntax.mkNumLit <| toString j
    let jLitSucc := Syntax.mkNumLit <| toString (j+1)
    try
      evalTactic $ ← `(tactic |  slice_lhs_aux $jLit et $jLitSucc avec $h)
      return
    catch _ =>
      restoreState s

    try
      evalTactic $ ← `(tactic |  slice_rhs_aux $jLit et $jLitSucc avec $h)
      return
    catch _ =>
      restoreState s
  restoreState s0
  throwError "ça ne marche pas encore"
