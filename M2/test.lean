import Lean
import Mathlib.Tactic
import Mathlib.CategoryTheory.Category.Basic



import Mathlib.Tactic.Widget.CommDiag
import ProofWidgets.Component.Panel.SelectionPanel
import ProofWidgets.Component.Panel.GoalTypePanel

open CategoryTheory Lean Meta Elab Tactic Widget

universe u v

variable (Cat : Type u) [Category.{v} Cat]  --[Small.{v, u} C]



variable (A B C D E F G H : Cat) (a : A ⟶ D) (b : A ⟶ C) (c : A ⟶ B) (d : B ⟶ C) (e : C ⟶ E) (f : B ⟶ F) (h : F ⟶ E) (i : E ⟶ G) (j : D ⟶ G) (k : F ⟶ G) (l : G ⟶ H) (m : B ⟶ G) (n : B ⟶ H)


--cc et rw_search ne marchent pas
lemma test (h1 : c ≫ d = b) (h2 : b ≫ e = a ≫ g) (h3 : d ≫ e = f ≫ h) (h4 : g ≫ i = j) (h5 : h ≫ i = k) (h6 : f ≫ k = m) (h7 : m ≫ l = n) : a ≫ j ≫ l = c ≫ n:= by

  rw [←  h7, ← h6, ← h5, ← Category.assoc f h i, ←  h3, ← h4, ← Category.assoc a _ l, ← Category.assoc a g i,  ← h2, ← h1]
  --rw_search { maxHeartbeats := 100}
  repeat rw [Category.assoc]

--#check [a,b]
/-
#widget Mathlib.Tactic.Widget.mkCommDiag
example (h: c ≫ d = b) : True := by
  #widget Mathlib.Tactic.Widget.mkCommDiag
  sorry-/

#check a ≫ j

#check (@CategoryStruct.toQuiver Cat _)

def bidule:= @Quiver.Hom.{v + 1, u} Cat (@CategoryStruct.toQuiver Cat _)

#check bidule


def match_comp (e: Expr) : MetaM <| Option (Expr × Expr) := do
  let cat := mkConst ``Cat
  let hom := mkConst ( ``bidule )
  --let a ← mkFreshExprMVar cat
  --let b ← mkFreshExprMVar cat
  --let c ← mkFreshExprMVar cat
  --let d ← mkFreshExprMVar cat
  let f ← mkFreshExprMVar hom
  let g ← mkFreshExprMVar hom

  let eq ← mkAppM ``Eq #[f,g]
  if ← isDefEq eq e then
    return some (f,g)
  else
    return none

#check  Expr.app7?
#check 1


elab "match_comp" : tactic => withMainContext do
  match ← match_comp (← getMainTarget) with
    | some (a, b) =>
      logInfo m!"Matched composition f≫ g; f = {a}, g= {b}"
    |none =>
      logWarning m!"Main target not of the corect form"

example : c ≫ d = b := by
  match_comp
  sorry

elab "cheat" : tactic => withMainContext do
  setGoals []


example : 1 = 2 := by
  cheat


def match_eq (e : Expr) : MetaM <| Option (Expr × Expr) := do
  let e ← whnf e
  if e.isAppOf ``Eq then
    return some (e.getArg! 1, e.getArg! 2)
  else
    return none

def match_eq' (e : Expr) : MetaM <| Option (Expr × Expr × Expr) := do
  let e ← whnf e
  if e.isAppOf ``Eq then do
    let e' := e.getArg! 1
    if e'.isAppOf ``CategoryStruct.comp then
      return some (e'.getArg! 5, e'.getArg! 6, e.getArg! 2)
    else
      return none
  else
    return none
