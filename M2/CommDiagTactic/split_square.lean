import Mathlib.Tactic

open CategoryTheory Lean Meta Elab Tactic

/-- check if the expression is of the form a ≫ b = c ≫ d and gives c and d-/
def is_square_lhs (e : Expr) : Option ( Expr × Expr) := do

  guard <| e.isAppOf ``Eq
  let e1 := e.getArg! 1
  let e2 := e.getArg! 2

  guard <| e1.isAppOf ``CategoryStruct.comp && e2.isAppOf ``CategoryStruct.comp
  return (e2.getArg! 5, e2.getArg! 6)

/-- If e is of the form a ≫ b = c ≫ d the morphisme c ≫ d is renamed e.map and e is replaced by
e.map_eq_right: a ≫ b = e.map and e.map_eq_left : c ≫ d = e.map-/
def split_square_step (_ : Unit ) (e : Expr) : TacticM Unit := withMainContext do
  match is_square_lhs (← inferType (← whnf e)) with
    |some (c, d) =>
      let hname  ← e.fvarId!.getUserName
      let hmap := hname.str   "map"
      let hleft := hname.str "map_eq_left"
      let hright := hname.str "map_eq_right"

      evalTactic $ ← `(tactic|set $(mkIdent hmap) := $( ← Term.exprToSyntax c) ≫ $( ← Term.exprToSyntax d) with ← $(mkIdent hright))
      evalTactic $ ← `(tactic|rename' $(mkIdent hname) => $(mkIdent hleft))

    | none => return ()

/--Apply the split_squre_step to all the "squares in the local context"-/
elab "split_square" : tactic => withMainContext do
  let hyp ← getLocalHyps
  let _ ←  Array.foldlM (split_square_step) () hyp
