import Lean
import Mathlib.Tactic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Tactic.CategoryTheory.Slice
import M2.Meta

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



def machinTactic (target: Expr)(tac: Syntax):
  TermElabM (Option (Nat × Nat)) :=
    withoutModifyingState do

    return some (1, 2)

syntax (name:= machin) "machin" tacticSeq : tactic

--def as: TSyntax `Lean.Parser.Tactic.tacticSeq := assumption

@[tactic machin] def machinImpl : Tactic :=
  fun stx => do
  match stx with
  | `(tactic| machin $tac) =>
    let n? ← machinTactic (← getMainTarget) tac
    match n? with
    | some (a, b) =>
      logInfo m!"un message"
      TryThis.addSuggestion stx tac
    | none =>
      logWarning m!"Tactic failed"
  | _ => throwUnsupportedSyntax





example : 2 ≤ 20 := by
  machin decide

  simp

/- the four morphism of the square 1≫ 2= 3≫ 4 of type 5-/
def is_square (e:Expr) : MetaM <| Option (Expr × Expr × Expr × Expr × Expr):= do
  --let e ← whnf e
  if e.isAppOf ``Eq then
    let e1 := e.getArg! 1
    let e2 := e.getArg! 2
    match e1.isAppOf ``CategoryStruct.comp , e2.isAppOf ``CategoryStruct.comp with
      | true, true => return some (e1.getArg! 5, e1.getArg! 6, e2.getArg! 5, e2.getArg! 6, ← inferType e1)
      | _, _ => return none -- un triangle ou autres chose
  else
    return none

elab "split_square" h:ident":" t:term : tactic => do

  let hmap : Name := Name.str h.getId  "map"
  let hleft : Name := Name.str h.getId  "map_eq_left"
  let hright : Name := Name.str h.getId  "map_eq_right"



  withMainContext do
    let goal ← getMainGoal
    let t ← elabType t

    let (ta,tb,tc,td,homType) ← ← is_square t
    let diag ← mkFreshExprMVar homType MetavarKind.syntheticOpaque hmap

    --withLocalDecl hmap .default homType (fun )

    let (diagId, newGoal) ← MVarId.intro1P $ ← goal.assert hmap homType diag
    replaceMainGoal [diag.mvarId!, newGoal]
    closeMainGoal `exact (t.getArg! 1)

    withMainContext do
    let diagDecl ←  diagId.getDecl
    let leftEq ← mkAppM `Eq #[ ← mkAppM ``CategoryStruct.comp #[ta,tb], diagDecl.toExpr]--

    let leftEqMv ← mkFreshExprMVar leftEq MetavarKind.syntheticOpaque hleft
    let goal ← getMainGoal
    let (_, newGoal) ← MVarId.intro1P $ ← goal.assert hleft leftEq leftEqMv
    replaceMainGoal [leftEqMv.mvarId!, newGoal]
    evalTactic $ ← `(tactic| sorry)

    withMainContext do
    let rightEq ← mkAppM `Eq #[ ← mkAppM ``CategoryStruct.comp #[tc,td],diagDecl.toExpr]--

    let rightEqMv ← mkFreshExprMVar rightEq MetavarKind.syntheticOpaque hright
    let goal ← getMainGoal
    let (_, newGoal) ← MVarId.intro1P $ ← goal.assert hright rightEq rightEqMv
    replaceMainGoal [rightEqMv.mvarId!, newGoal]
    evalTactic $ ← `(tactic| sorry)

#check elabTerm

def find_triangles ( _ : Unit) (e: Expr) : TacticM Unit := withMainContext do
  let txt := s!"{ ← ppExpr e } : { ← inferType e}"
  evalTactic $ ← `(tactic | try split_square `( ← ppExpr e) : elabterm e )

  return ()

elab "split" : tactic => withMainContext do
  let hyp ← getLocalHyps
  let _ ←   Array.foldlM (find_triangles) () hyp



#check Array.foldlM
#check liftMetaTactic


variable (a: A ⟶ B) (b: B ⟶ C) (c: A ⟶ D ) (d : D ⟶ C)

example (h : a ≫ b =  c ≫ d) : a ≫ b = c ≫ d := by
  --split



  split_square h:  a ≫ b = c ≫ d

  rw [h.map_eq_left,h.map_eq_right]

  --decide

  --sorry




















  --sorry


#check mkConst
#expr [a]

variable (A B C D E F G H : Cate) (a : A ⟶ D) (b : A ⟶ C) (c : A ⟶ B) (d : B ⟶ C) (e : C ⟶ E) (f : B ⟶ F) (h : F ⟶ E) (i : E ⟶ G) (j : D ⟶ G) (k : F ⟶ G) (l : G ⟶ H) (m : B ⟶ G) (n : B ⟶ H)


lemma test (h1 : c ≫ d = b) (h2 : b ≫ e = a ≫ g) (h3 : d ≫ e = f ≫ h) (h4 : g ≫ i = j) (h5 : h ≫ i = k) (h6 : f ≫ k = m ) (h7 : m ≫ l = n) : a ≫ j ≫ l = c ≫ n:= by

  GetPath
