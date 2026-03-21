import Lean.Elab.Tactic.Basic
import Mathlib.CategoryTheory.Limits.HasLimits

open CategoryTheory CategoryTheory.Limits Opposite Lean Meta Elab Tactic

universe u v w x

/-- try to identify e as lim.π F a ≫ _  = lim.π F b and return the parameters-/
def is_limitwLeft (e : Expr) : MetaM <| Expr × Expr := do
  let e ← whnf e
  guard <| e.isAppOfArity ``Eq 3
  let e1 := e.getArg! 1
  let e2 := e.getArg! 2
  guard <| e1.isAppOfArity ``CategoryStruct.comp 7 && e2.isAppOfArity ``CategoryTheory.Limits.limit.π 7
  let limLeft := e1.getArg! 5
  guard <| limLeft.isAppOfArity ``CategoryTheory.Limits.limit.π 7
  -- if the two functor on wich the colimits are taken are equal
  guard <| ← isDefEq (limLeft.getArg! 4) (e2.getArg! 4)
  return (e2.getArg! 6, limLeft.getArg! 6)

/-- if the main target is of the form _ ≫ colim.ι F a = colim.ι F b, then try to solve it by forcing the application of the colimit.w lemma-/
def forceLimWLeft : TacticM Unit := withMainContext do
  let (a,b) ← is_limitwLeft (← getMainTarget)
  let fForce := "fForce".toName
  -- make the intermediate goal fForce : b ⟶ a
  let newtarget ← mkAppM ``Quiver.Hom #[b, a]
  let newGoal ← mkFreshExprMVar newtarget
  appendGoals [newGoal.mvarId!]

  -- apply the limit.w lemma and try to solve it
  evalTactic <| ← `(tactic| let $(⟨mkIdent fForce⟩) := $( ← Term.exprToSyntax newGoal))
  evalTactic <| ← `(tactic| rw [ ← limit.w _ $(mkIdent fForce)]; apply whisker_eq; first | aesop_cat| skip)

  match ← getUnsolvedGoals with -- maybe the aesop_cat tactic closed everything if the morphism is obvious
    |[] => return
    | _ => -- go to the morphism goal (if it is already solved by the previous simplifications ) and the try to solve it
      evalTactic $ ← `(tactic| first | swap| skip)
      evalTactic $ ← `(tactic| first |assumption | apply Opposite.op | skip)
      evalTactic $ ← `(tactic| first | apply CategoryTheory.homOfLE | skip)
      evalTactic $ ← `(tactic| first | aesop_cat | skip)

elab "forceLimW" : tactic => withMainContext do
  let s0 ← saveState
  evalTactic $ ←  `(tactic| (repeat rw [ Category.assoc]); repeat apply whisker_eq)
  try
    forceLimWLeft
  catch
    | _ => try
            evalTactic $ ←  `(tactic| apply Eq.symm)
            forceLimWLeft
          catch
            | _ => restoreState s0
                   throwError "The goal is not of the form  limit.π F x ≫ _= limit.π F y"

/-
variable {C : Type u} [Category.{v, u} C] {D : Type w} [Category.{x, w} D] (F : Cᵒᵖ  ⥤ D) [HasLimit F] { a b : C} ( f: b ⟶ a)

def FfBis : F.obj (op a) ⟶ F.obj ( op b) := let truc := f;sorry--F.map (op f)

example :  ((limit.π  F ( op a)) ≫ FfBis F f) ≫ 𝟙 _= limit.π  F (op b) := by
  forceLimW
  sorry
example : 1=1 := by forceLimW-/
