import Lean
import Mathlib.Tactic
import Mathlib.CategoryTheory.Category.Basic

open CategoryTheory Lean Meta Elab Tactic


variable (Cat : Type ) [Category Cat]  --[Small.{v, u} C]



variable (A B C D E F G H : Cat) (a : A ⟶ D) (b : A ⟶ C) (c : A ⟶ B) (d : B ⟶ C) (e : C ⟶ E) (f : B ⟶ F) (h : F ⟶ E) (i : E ⟶ G) (j : D ⟶ G) (k : F ⟶ G) (l : G ⟶ H) (m : B ⟶ G) (n : B ⟶ H)


--cc et rw_search ne marchent pas (j'ai poussé à set_option maxHeartbeats 1000000000 in)
lemma test (h1 : c ≫ d = b) (h2 : b ≫ e = a ≫ g) (h3 : d ≫ e = f ≫ h) (h4 : g ≫ i = j) (h5 : h ≫ i = k) (h6 : f ≫ k = m) (h7 : m ≫ l = n) : a ≫ j ≫ l = c ≫ n:= by

  rw [←  h7, ← h6, ← h5, ← Category.assoc f h i, ←  h3, ← h4, ← Category.assoc a _ l, ← Category.assoc a g i,  ← h2, ← h1]

  repeat rw [Category.assoc]



#check a ≫ j

#check (@CategoryStruct.toQuiver Cat _)

def bidule:= @Quiver.Hom Cat (@CategoryStruct.toQuiver Cat _)

#check bidule


def match_comp (e: Expr) : MetaM <| Option (Expr × Expr × Expr) := do
  --let cat := mkConst ``Cat

  --let hom ←  mkFreshTypeMVar
  --let f ← mkFreshExprMVar hom
  --let g ← mkFreshExprMVar hom
  --let h ← mkFreshExprMVar hom

  let t1 ← mkFreshTypeMVar
  let t2 ← mkFreshTypeMVar
  let t3 ← mkFreshTypeMVar
  --let t4 ← mkFreshTypeMVar
  --let t5 ← mkFreshTypeMVar

  let hom1 ← mkAppM ``Quiver.Hom #[t1, t2]
  let hom2 ← mkAppM ``Quiver.Hom #[t2, t3]
  let hom3 ← mkAppM ``Quiver.Hom #[t1, t3]

  let f ← mkFreshExprMVar hom1
  let g ← mkFreshExprMVar hom2
  let h ← mkFreshExprMVar hom3

  let comp ← mkAppM ``CategoryStruct.comp #[f, g]
  if (← isDefEq (← mkAppM ``Eq #[comp, h]) e) || (← isDefEq (← mkAppM ``Eq #[h, comp]) e) then
    return some (f,g,h)
  else
    return none

#check  Expr.app7?
#check 1
#check A ⟶ B


elab "match_comp" : tactic => withMainContext do
  match ← match_comp (← getMainTarget) with
    | some (a, b, c) =>
      logInfo m!"Matched composition f≫ g= h; f = {a}, g = {b} et h = {c}"
    |none =>
      logWarning m!"Main target not of the corect form"

example : c ≫ d = b := by
  match_comp
  sorry

elab "cheat" : tactic => withMainContext do
  setGoals []


example : 1 = 2 := by
  cheat


example (h : A = B) : b = d := by sorry
