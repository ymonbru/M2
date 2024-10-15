import Lean
import Mathlib.Tactic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Tactic.CategoryTheory.Slice

open CategoryTheory Lean Meta Elab Tactic Term


variable (Cate : Type  ) [Category Cate]  --[Small.{v, u} C]



variable (A B C D E F G H : Cate) (a : A ⟶ D) (b : A ⟶ C) (c : A ⟶ B) (d : B ⟶ C) (e : C ⟶ E) (f : B ⟶ F) (h : F ⟶ E) (i : E ⟶ G) (j : D ⟶ G) (k : F ⟶ G) (l : G ⟶ H) (m : B ⟶ G) (n : B ⟶ H)


--cc et rw_search ne marchent pas (j'ai poussé à set_option maxHeartbeats 1000000000 in)
lemma test (h1 : c ≫ d = b) (h2 : b ≫ e = a ≫ g) (h3 : d ≫ e = f ≫ h) (h4 : g ≫ i = j) (h5 : h ≫ i = k) (h6 : f ≫ k = m) (h7 : m ≫ l = n) : a ≫ j ≫ l = c ≫ n:= by

  rw [←  h7, ← h6, ← h5, ← Category.assoc f h i, ←  h3, ← h4, ← Category.assoc a _ l, ← Category.assoc a g i,  ← h2, ← h1]

  repeat rw [Category.assoc]



#check a ≫ j

#check (@CategoryStruct.toQuiver Cate _)

def qhc:= @Quiver.Hom Cate (@CategoryStruct.toQuiver Cate _)

#check @Quiver.Hom

#check (c : qhc Cate A B)

#check (A : Cate)

--variable (Truc: Type) [Category Truc] (A B : Truc)

--#check Quiver.Hom A B
--#check Category Truc

def matchexpr (e : Expr) : MetaM <| Option (Expr × Expr):= do
  --let cat := mkConst ``Cat [← mkFreshLevelMVar, ← mkFreshLevelMVar]
  let cat ← mkFreshTypeMVar

  --let inst ← mkAppM ``Category #[cat]


  let c ← mkFreshExprMVar cat
  let A ← mkFreshExprMVar c
  let B ← mkFreshExprMVar c
  let inst ← mkFreshTypeMVar


  let hom1 ← mkAppM ``Quiver.Hom #[c, inst, A, B]

  let f ← mkFreshExprMVar hom1
  let g ← mkFreshExprMVar hom1

  if (← isDefEq (← mkAppM ``Eq #[f, g]) e) then
    return some (f,g)
  else
    return none

elab "matchexpr" : tactic => withMainContext do
  match ← matchexpr (← getMainTarget) with
    | some (a, b) =>
      logInfo m!"Matched composition f = g; f = {a}, g = {b}"
    |none =>
      logWarning m!"Main target not of the corect form"

example : c ≫ d = b := by
  matchexpr

  sorry


def match_comp (e: Expr) : MetaM <| Option (Expr × Expr × Expr) := do
  --let cat := mkConst ``Cat [← mkFreshLevelMVar, ← mkFreshLevelMVar]
  let cat ← mkFreshTypeMVar

  --let inst ← mkAppM ``Category #[cat]


  let c ← mkFreshExprMVar cat
  let A ← mkFreshExprMVar c
  let B ← mkFreshExprMVar c
  let C ← mkFreshExprMVar c
  let inst ← mkFreshTypeMVar


  let hom1 ← mkAppM ``Quiver.Hom #[c, inst, A, B]
  let hom2 ← mkAppM ``Quiver.Hom #[c, inst, B, C]
  let hom3 ← mkAppM ``Quiver.Hom #[c, inst, A, C]

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
      logInfo m!"Matched composition f ≫ g= h; f = {a}, g = {b} et h = {c}"
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


elab "#expr" "[" t:term "]" : command =>
  Command.liftTermElabM do
  let t ← Term.elabTerm t none
  let t ← instantiateMVars t
  logInfo m!"Expression: {t}:\n{repr t}"
  let t ← reduce t
  let t ← instantiateMVars t
  logInfo m!"Reduced: {t}:\n{repr t}"



def checkTactic (target: Expr)(tac: Syntax):
  TermElabM (Option Nat) := do
    try
      let goal ← mkFreshExprMVar target
      let (goals, _) ←
        withoutErrToSorry do
        Elab.runTactic goal.mvarId! tac
          (← read) (← get)
      return some goals.length
    catch _ =>
      return none

elab "check_tactic" tac:tacticSeq : tactic => do
  let n? ← checkTactic (← getMainTarget) tac
  match n? with
  | some n =>
    logInfo m!"Tactic succeeded; {n} goals remain"
  | none =>
    logWarning m!"Tactic failed"

example : 2 ≤ 20 := by
  check_tactic decide

  simp
