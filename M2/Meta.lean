import Lean
import Mathlib.Tactic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Tactic.CategoryTheory.Slice
import M2.Comm_rw

open CategoryTheory Lean Meta Elab Tactic


/-- check if an expression is a sequence of composition of morphisms and gives the list-/
partial def match_comp (e : Expr) : MetaM <|(List Expr) := do
  if e.isAppOf ``CategoryStruct.comp then
    return (← match_comp (e.getArg! 5)) ++ (← match_comp (e.getArg! 6)) -- probablement pas optimal du tout
  else
    return [e]

/-- check if an expression is an equality of composition of morphisms and gives the two sequences-/
def match_eq (e : Expr) : MetaM <| Option (List Expr × List Expr) := do
  let e ← whnf e
  if e.isAppOf ``Eq then
    return some (← match_comp (e.getArg! 1) , ← match_comp (e.getArg! 2))
  else
    return none


/-- check if the expression is of the form a ≫ b = c ≫ d and gives c and d-/
def is_square_lhs (e : Expr) : MetaM <| Option ( Expr × Expr) := do
  let e ← whnf e
  if e.isAppOf ``Eq then
    let e1 := e.getArg! 1
    let e2 := e.getArg! 2
    match e1.isAppOf ``CategoryStruct.comp , e2.isAppOf ``CategoryStruct.comp with
      | true, true => return (e2.getArg! 5, e2.getArg! 6)
      | true, _ => return none
      | _, true => return none
      | _, _ => return none
  else
    return none

/-- build a data structure triangle (from M2.Comm_rw) that represent the composition h : e.1 ≫ e.2.1 =e.2.2-/
def toTrg (e : Expr × Expr × Expr ) (h : Expr) : MetaM (triangle):= do
  return ⟨e.1 ,e.2.1 ,e.2.2, h⟩

/-- a step in FindPath that add to the list the triangle coresponding to e if it represents a triangle  -/
def find_triangles_totrig (l : List triangle ) (e: Expr) : MetaM <|List triangle := do
  match ← is_triangle ( ← inferType e) with
    | some <| (f , g, h) =>  return  ( ← toTrg (f, g, h) e) :: l
    | none =>  return l

/-def find_triangles (l : List (Expr × Expr × Expr)) (e: Expr) : MetaM <|List (Expr × Expr × Expr) := do
  match ← is_triangle ( ← inferType e) with
    | some <| (f , g, h) =>
      logInfo m!"one triangle is {f} ≫ {g} = {h}"
      return  (f, g, h) :: l
    | none =>  return l

elab "find_triangles" : tactic => withMainContext do
  let hyp ← getLocalHyps
  let list_triangles :=  Array.foldlM (find_triangles) [] hyp
  logInfo m!" the triangles are { ← list_triangles}"-/


/-- If e is of the form a ≫ b = c ≫ d the morphisme c ≫ d is renamed e.map and e is replaced by
e.map_eq_right: a ≫ b = e.map and e.map_eq_left : c ≫ d = e.map-/
def split_square_step (_ : Unit ) (e : Expr) : TacticM Unit := withMainContext do
  match ← is_square_lhs (← inferType e) with
    |some (c, d) =>
      let hname := s!"{← ppExpr e}"
      let hmap := Name.str hname.toName   "map"
      let hleft  := Name.str hname.toName "map_eq_left"
      let hright := Name.str hname.toName  "map_eq_right"

      evalTactic $ ← `(tactic|set $(mkIdent hmap) := $( ← Term.exprToSyntax c) ≫ $( ← Term.exprToSyntax d) with ← $(mkIdent hright))
      evalTactic $ ← `(tactic|rename' $(mkIdent hname.toName) => $(mkIdent hleft))

    | none => return ()

/--Apply the split_squre_step to all the "squares in the local context"-/
elab "split_square" : tactic => withMainContext do
  let hyp ← getLocalHyps
  let _ ←  Array.foldlM (split_square_step) () hyp

/-- Split all the square if needed then find the triangles and use the algo CommDiag to show the goal-/
elab "FindPath" : tactic => withMainContext do
  evalTactic $ ← `(tactic| split_square)

  withMainContext do-- beacause the context has changed
  let hyp ← getLocalHyps
  let list_triangles :=  Array.foldlM (find_triangles_totrig) [] hyp
  let list_hom ← ← match_eq (← getMainTarget)

  let _ ←  CommDiag  ( ← list_triangles) list_hom.1
  --let _ ←  CommDiag  ( ← list_triangles) list_hom.2

  evalTactic $ ← `(tactic| repeat rw [Category.assoc])


 /- Exemples -/

variable (Cat : Type ) [Category Cat]

variable (A B C D E F G H : Cat) (a : A ⟶ D) (b : A ⟶ C) (c : A ⟶ B) (d : B ⟶ C) (e : C ⟶ E) (f : B ⟶ F) (h : F ⟶ E) (i : E ⟶ G) (j : D ⟶ G) (k : F ⟶ G) (l : G ⟶ H) (m : B ⟶ G) (n : B ⟶ H)

lemma test (h1 : c ≫ d = b) (h2 : b ≫ e = a ≫ g) (h3 : d ≫ e = f ≫ h) (h4 : g ≫ i = j) (h5 : h ≫ i = k) (h6 : f ≫ k = m ) (h7 : m ≫ l = n) : a ≫ j ≫ l = c ≫ n:= by
  /-split_square

  rw [← h7, ← h6, ← h5,]
  rw_assoc2 h3.map_eq_right
  rw [← h3.map_eq_left]
  rw_assoc2 h1
  rw_assoc2 h2.map_eq_left
  rw[← h2.map_eq_right]
  rw_assoc h4

  repeat rw [Category.assoc]-/

  FindPath



  --rw [←  h7, ← h6, ← h5, ← Category.assoc f h i, ←  h3, ← h4, ← Category.assoc a _ l, ← Category.assoc a g i,  ← h2, ← h1]
  --repeat rw [Category.assoc]

variable (a : A ⟶ B) (b : A ⟶ C) (c : B ⟶ C) (d : B ⟶ D) (e : D ⟶ C) (f : C ⟶ E) (g : D ⟶ E) (h : E ⟶ F) (i : D ⟶ F) (j : D ⟶ G) (k : F ⟶ G)

lemma test23 (h1 : a ≫ c  = b) (h2 : d ≫ e = c) (h3 : e ≫ f = g) (h4 : g ≫ h = i) (h5 :  i ≫ k = j ) : a ≫  d ≫ j = b ≫ f ≫ h ≫ k := by

  FindPath


  --rw [ ← h5, ← h4, ← h3]
  --rw_assoc h2
  --rw_assoc h1
  --repeat rw [Category.assoc]

variable (a : A ⟶ B) (b : B ⟶ D) (c : C ⟶ D) (d: A ⟶ C) (e: C ⟶ B)

lemma test3 (h1 : d ≫ e = a) (h2 : e ≫ b = c): a ≫ b = d ≫ c := by
  FindPath
