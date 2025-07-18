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
def reqLength (e : Expr) : MetaM Nat := do
  let e ← whnf e
  if e.isAppOf ``Eq then
    return max (← compLength (e.getArg! 1)) (← compLength (e.getArg! 2))
  else
    return 0

/-- check if the expression correspond to  a ≫ b = c or c = a ≫ b and gives the three morphisms involved -/
def is_triangle (e : Expr) : MetaM <| Option ( Expr × Expr × Expr × Bool) := do
  let e ← whnf e
  if e.isAppOf ``Eq then
    let e1 := e.getArg! 1
    let e2 := e.getArg! 2
    match e1.isAppOf ``CategoryStruct.comp , e2.isAppOf ``CategoryStruct.comp with
      | true, true => return none
      | true, _ => return (e1.getArg! 5, e1.getArg! 6, e2, true)
      | _, true => return (e2.getArg! 5, e2.getArg! 6, e1, false)
      | _, _ => return none
  else
    return none

def or_option (a b : Option Nat) (diff : Nat): MetaM <| Option Nat := match a, b with
  |_, none => return a
  |none, some b => return b + diff

  |some a, some b => do
    logInfo m!"There is a cycle: the same morphism is in position {a} and {b}"
    return max a b


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

elab "rw_assoc" h:term : tactic => withMainContext do
  let goal ← whnf (← getMainTarget)

  guard <| goal.isAppOf ``Eq
  let hTerm ← elabTerm h none
  let hType ← inferType hTerm

  match (← is_triangle hType) with
    | none => return ()
    | some (a, b, _) =>
      let e1 := goal.getArg! 1
      let e2 := goal.getArg! 2

      let (_, aInl?,bInl?) ← findAB e1 a b
      let (_, aInr?,bInr?) ← findAB e2 a b

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

      return ()

elab "rw_assoc_lhs" h:term : tactic => withMainContext do
  let goal ← whnf (← getMainTarget)

  guard <| goal.isAppOf ``Eq
  let hTerm ← elabTerm h none
  let hType ← inferType hTerm

  match (← is_triangle hType) with
    | none => return ()
    | some (a, b, _) =>
      let e1 := goal.getArg! 1

      let (_, aInl?, bInl?) ← findAB e1 a b

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
      catch _ =>
        restoreState s
        return

elab "rw_assoc_rhs" h:term : tactic => withMainContext do
  let goal ← whnf (← getMainTarget)

  guard <| goal.isAppOf ``Eq
  let hTerm ← elabTerm h none
  let hType ← inferType hTerm

  match (← is_triangle hType) with
    | none => return ()
    | some (a, b, _) =>

      let e2 := goal.getArg! 2
      let (_, aInr?, bInr?) ← findAB e2 a b

      let s ← saveState
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
      catch _ =>
        restoreState s
        return

def rw_assoc_lhs_suggest (h : Term) : TacticM <| Option <| TSyntax `tactic := withMainContext do
  let goal ← whnf (← getMainTarget)


  guard <| goal.isAppOf ``Eq
  let hTerm ← elabTerm h none
  let hType ← inferType hTerm


  match (← is_triangle hType) with
    | none => return none
    | some (a, b, _) =>

      let e1 := goal.getArg! 1

      let (_, aInl?, bInl?) ← findAB e1 a b
      logInfo m!"{← ppExpr e1}, {a}, {b}"
      match aInl?, bInl? with
        | none, _ => logInfo m!" a not found"
        | _, none =>  logInfo m!" b not found"
        | some a, some b =>
          if b = a + 1 then
            let aLit := Syntax.mkNumLit <| toString a
            let bLit := Syntax.mkNumLit <| toString b

            return some (← `(tactic |  slice_lhs $aLit $bLit => first | rw [ ($h)] | rw [ ← ($h)]))

          else throwError "a and b not next to each other"

     return none
