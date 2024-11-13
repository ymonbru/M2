import Lean
import Mathlib.Tactic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Tactic.CategoryTheory.Slice

open CategoryTheory Lean Meta Elab Tactic

/- rwassoc2  seems to be more eficient than rwassoc -/

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

/-- check if the expression correspond to  a ≫ b = c or c = a ≫ b and gives the three morphisms involved -/
def is_triangle (e : Expr) : MetaM <| Option ( Expr × Expr × Expr) := do
  let e ← whnf e
  if e.isAppOf ``Eq then
    let e1 := e.getArg! 1
    let e2 := e.getArg! 2
    match e1.isAppOf ``CategoryStruct.comp , e2.isAppOf ``CategoryStruct.comp with
      | true, true => return none
      | true, _ => return (e1.getArg! 5, e1.getArg! 6, e2)
      | _, true => return (e2.getArg! 5, e2.getArg! 6, e1)
      | _, _ => return none
  else
    return none

def or_option (a b : Option Nat) (diff : Nat): MetaM <| Option Nat := match a, b with
  |_, none => return a
  |none, some b => return b + diff

  |some a, some b => do
    logInfo m!"There is a cycle: the same morphism is in position {a} and {b}"
    return max a b


#eval or_option none (some 23) 4

partial def findAB (e a b: Expr) : MetaM <| Nat × Option Nat × Option Nat := do
    --let e ← whnf e --ça le reste n'aime pas

    if e.isAppOf ``CategoryStruct.comp then
      let (n1, aIn1?, bIn1?) ← ( findAB (e.getArg! 5 ) a b)
      let (n2, aIn2?, bIn2?) ← ( findAB (e.getArg! 6 ) a b)

      return (n1 + n2, ← or_option aIn1? aIn2? n1,← or_option bIn1? bIn2? n1)
    else
      if ← isDefEq e a then
        return (1,some 1,none)
      else
        if ← isDefEq e b then
          return (1, none, some 1)
        else
          return (1, none,  none)





elab "rw_assoc2" h:term : tactic => withMainContext do
  let goal ← whnf (← getMainTarget)

  if goal.isAppOf ``Eq then
    let hTerm ← elabTerm h none
    let hType ← inferType hTerm

    match (← is_triangle hType) with-- avec Option.mapM ?
      | none => return ()
      | some (a, b, _) =>
        let e1 := goal.getArg! 1
        let e2 := goal.getArg! 2

        let (x1,aInl?,bInl?) ← findAB e1 a b
        let (x2,aInr?,bInr?) ← findAB e2 a b

        let s ← saveState
        try
          match aInl?, bInl? with
            | none, _ => throwError " a not found"
            | _, none => throwError " b not found"
            | some a, some b =>
              if b = a + 1 then
                let aLit := Syntax.mkNumLit <| toString a
                let bLit := Syntax.mkNumLit <| toString b

                evalTactic $ ← `(tactic |  slice_lhs $aLit $bLit => first | rw [ ($h)] | rw [ ← ($h)])
                return
              else throwError "a and b not next to each other"
        catch _ => restoreState s

        try
          match aInr?, bInr? with
            | none, _ => throwError " a not found"
            | _, none => throwError " b not found"
            | some a, some b =>
              if b = a + 1 then
                let aLit := Syntax.mkNumLit <| toString a
                let bLit := Syntax.mkNumLit <| toString b

                evalTactic $ ← `(tactic |  slice_rhs $aLit $bLit => first | rw [ ($h)] | rw [ ← ($h)])
                return
              else throwError "a and b not next to each other"
        catch _ => restoreState s

        --logInfo m!"{x1},{x2} {aInl?},{bInl?},{aInr?},{bInr?}"
        return ()
      else
        return ()
