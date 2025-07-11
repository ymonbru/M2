import Mathlib

open CategoryTheory CategoryTheory.Limits Opposite Lean Meta Elab Tactic

universe u v w x

def is_colimitwLeft (e : Expr) : MetaM <| Option ( Expr × Expr) := do
  let e ← whnf e
  if e.isAppOf ``Eq then
    let e1 := e.getArg! 1
    let e2 := e.getArg! 2
    match e1.isAppOf ``CategoryStruct.comp , e2.isAppOf ``CategoryTheory.Limits.colimit.ι with
      | true, true =>
        let colimLeft := e1.getArg! 6
        if colimLeft.isAppOf ``CategoryTheory.Limits.colimit.ι then

          -- if the two functor on wich the colimits are taken are equal
          if ← isDefEq (colimLeft.getArg! 4) (e2.getArg! 4) then
            return (e2.getArg! 6, colimLeft.getArg! 6)
          else
            return none
        else
          return none
      | true, _ => return none
      | _, true => return none
      | _, _ => return none
  else
    return none


elab "forceColimW" : tactic => withMainContext do
  let s0 ← saveState
  evalTactic $ ←  `(tactic| repeat rw [ ← Category.assoc])
  match ← is_colimitwLeft (← getMainTarget) with
    | none => restoreState s0; throwError "The goal is not of the form _ ≫ colimit.ι F x = colimit.ι F y"
    | some (a,b) =>
      let fForce := "fForce".toName

      -- make the intermediate goal fForce : a ⟶ b
      let newtarget ← mkAppM ``Quiver.Hom #[a, b]
      let newGoal ← mkFreshExprMVar newtarget
      appendGoals [newGoal.mvarId!]

      -- apply the colimit.w lemma and try to solve it
      evalTactic $ ← `(tactic| set $(mkIdent fForce) := $( ← Term.exprToSyntax newGoal))
      evalTactic $ ← `(tactic| rw [ ← colimit.w _ $(mkIdent fForce)]; apply eq_whisker; first | aesop_cat| skip)

      match ← getUnsolvedGoals with -- maybe the aesop_cat tactic closed everything if the morphism is obvious
        | [] => return

        | _ => -- go to the morphism goal an try to solve it
          evalTactic $ ← `(tactic| swap; first | apply Opposite.op | skip)
          evalTactic $ ← `(tactic| first | apply CategoryTheory.homOfLE | skip)
          evalTactic $ ← `(tactic| first | simp | skip)

variable {C : Type u} [Category.{v, u} C] {D : Type w} [Category.{x, w} D] (F : Cᵒᵖ  ⥤ D) [HasColimit F] { a b : C} ( f: b ⟶ a)

/-def FfBis : F.obj (op a) ⟶ F.obj ( op b) := let truc := f;sorry--F.map (op f)

example : (𝟙 _ ≫ (FfBis F f ≫ colimit.ι F ( op b)) = colimit.ι F (op a)) := by

  forceColimW


  exact f



  sorry
example : 1=1 := by forceColimW-/
