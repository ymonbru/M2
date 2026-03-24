import Lean.Elab.Tactic.Basic
import Mathlib.CategoryTheory.Limits.HasLimits


open CategoryTheory CategoryTheory.Limits Opposite Lean Meta Elab Tactic

universe u v w x

/-- try to identify e as _ ≫ colim.ι F a = colim.ι F b and return the parameters-/
def get_colimitwParamLeft (e : Expr) : TacticM <| Expr × Expr × Option Expr := do
  let e ← whnf e
  guard <| e.isAppOfArity ``Eq 3
  let e1 := e.getArg! 1
  let e2 := e.getArg! 2
  guard <| e1.isAppOfArity ``CategoryStruct.comp 7
  if e2.isAppOfArity ``CategoryTheory.Limits.colimit.ι 7 then
    let colimLeft := e1.getArg! 6
    guard <| colimLeft.isAppOfArity ``CategoryTheory.Limits.colimit.ι 7

    -- if the two functor on wich the colimits are taken are equal
    guard <| ← isDefEq (colimLeft.getArg! 4) (e2.getArg! 4)
    return (e2.getArg! 6, colimLeft.getArg! 6, none)
  else
    --in the case where it is not colim.ι bu c.ι with c a cocone
    guard <| e2.isAppOfArity ``CategoryTheory.NatTrans.app 8
    let ciR := e2.getArg! 6
    let ciAppL := e1.getArg! 6
    guard <| ciAppL.isAppOfArity ``CategoryTheory.NatTrans.app 8
    let ciL := ciAppL.getArg! 6

    guard <| ciL.isAppOfArity ``CategoryTheory.Limits.Cocone.ι 6 && ciR.isAppOfArity ``CategoryTheory.Limits.Cocone.ι 6

    -- if the two cones are equal
    guard <| ← isDefEq (ciL.getArg! 5) (ciR.getArg! 5)
    return (e2.getArg! 8, ciAppL.getArg! 8, ciL.getArg! 5)

/-- if the main target is of the form _ ≫ colim.ι F a = colim.ι F b, then try to solve it by forcing the application of the colimit.w lemma-/
def forceColimWLeft : TacticM Unit := withMainContext do
  let (a,b, c) ← get_colimitwParamLeft (← getMainTarget)
  let fForce := "fForce".toName
  -- make the intermediate goal fForce : a ⟶ b
  let newtarget ← mkAppM ``Quiver.Hom #[a, b]
  let newGoal ← mkFreshExprMVar newtarget
  appendGoals [newGoal.mvarId!]

  -- apply the colimit.w lemma and try to solve it
  evalTactic <| ← `(tactic| let $(mkIdent fForce) := $( ← Term.exprToSyntax newGoal))

  -- the con_rhs is there to ensure that if fForce is secretly the 𝟙 _ then the rw will not rewrite two times colimit.w
  match c with
    |none =>
      evalTactic <| ← `(tactic| conv_rhs => rw [ ← CategoryTheory.Limits.colimit.w _ $(mkIdent fForce)])
    |some c =>
      evalTactic <| ← `(tactic| conv_rhs => (rw [ ← CategoryTheory.Limits.Cocone.w ($( ← Term.exprToSyntax c)) $(mkIdent fForce)]))

  evalTactic <| ← `(tactic| apply eq_whisker; first | aesop_cat| skip)

  match ← getUnsolvedGoals with -- maybe the aesop_cat tactic closed everything if the morphism is obvious
        | [] => return
        | _ => -- go to the morphism goal (if it is already solved by the previous simplifications ) and the try to solve it

          evalTactic $ ← `(tactic| first | swap| skip)


          --La il faut trouver un algo intelligent
          evalTactic $ ← `(tactic| first | apply Opposite.op; constructor; apply Quiver.Hom.unop;assumption | apply Opposite.op; constructor; apply CategoryTheory.homOfLE|skip)
          --evalTactic $ ← `(tactic| first | apply Quiver.Hom.unop | apply Opposite.op | skip)
          --evalTactic $ ← `(tactic| first | apply CategoryTheory.homOfLE | skip)
          evalTactic $ ← `(tactic| first | aesop_cat | skip)

elab "forceColimW0": tactic => withMainContext do forceColimWLeft

elab "forceColimW" : tactic => withMainContext do
  let s0 ← saveState
  evalTactic $ ←  `(tactic| (repeat rw [ ← Category.assoc]); repeat apply eq_whisker)
  try
    forceColimWLeft
  catch
    | _ => try
            evalTactic $ ←  `(tactic| apply Eq.symm)
            forceColimWLeft
          catch
            | _ => restoreState s0
                   throwError "The goal is not of the form : _ ≫ cocone.ι F x = cocone.ι F y"

/-
variable {C : Type u} [Category.{v, u} C] {D : Type w} [Category.{x, w} D] (F : Cᵒᵖ  ⥤ D) [HasColimit F] { a b : C} ( f: b ⟶ a)

def FfBis : F.obj (op a) ⟶ F.obj ( op b) := let truc := f;sorry--F.map (op f)

variable (c: Cocone F)

example: FfBis F f ≫ c.ι.app (op b) = c.ι.app (op a) := by
  forceColimW
  sorry

example : (𝟙 _ ≫ (FfBis F f ≫ colimit.ι F ( op b)) = colimit.ι F (op a)) := by
  --repeat rw [ ← Category.assoc]
  --test


  forceColimW
  sorry



/- sorry
example : 1=1 := by forceColimW-/

/-variable (C J K: Type) [Category C] [Category J] [Category K] (F : J ⥤ C) (E: K ⥤ J) ( EggF : K ⥤ C) (k : K)

example : colimit.ι EggF k ≫ colimit.pre F E  = sorry := by sorry

#check colimit.ι_pre-/-/
