import Lean
import Mathlib.Tactic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Tactic.CategoryTheory.Slice
import M2.Comm_test

open CategoryTheory Lean Meta Elab Tactic


variable (Cat : Type ) [Category Cat]

variable (A B C D E F G H : Cat) (a : A ⟶ D) (b : A ⟶ C) (c : A ⟶ B) (d : B ⟶ C) (e : C ⟶ E) (f : B ⟶ F) (h : F ⟶ E) (i : E ⟶ G) (j : D ⟶ G) (k : F ⟶ G) (l : G ⟶ H) (m : B ⟶ G) (n : B ⟶ H)



def match_comp (e : Expr) : MetaM <|(List Expr) := do
  if e.isAppOf ``CategoryStruct.comp then
    return (← match_comp (e.getArg! 5)) ++ (← match_comp (e.getArg! 6)) -- probablement pas optimal du tout
  else
    return [e]
termination_by e
decreasing_by
  --ça devrait se faire tout seul non?
  · sorry
  · sorry

def match_eq (e : Expr) : MetaM <| Option (List Expr × List Expr) := do
  let e ← whnf e
  if e.isAppOf ``Eq then
    return some (← match_comp (e.getArg! 1) , ← match_comp (e.getArg! 2))
  else
    return none

#check MonadLCtx.getLCtx


elab "match_eq" : tactic => withMainContext do
  match ← match_eq (← getMainTarget) with
    | some (a, b) =>
      logInfo m!"It's an equality of compostion, the first sequence is = {a}, and the second one is {b}"
    |none =>
      logWarning m!"Main target not of the corect form"

def is_triangle (e:Expr) : MetaM <| Option (Expr × Expr × Expr):= do
  --let e ← whnf e
  if e.isAppOf ``Eq then
    let e1 := e.getArg! 1
    let e2 := e.getArg! 2
    match e1.isAppOf ``CategoryStruct.comp , e2.isAppOf ``CategoryStruct.comp with
      | true, true => return none --un carré pas un triangle (donc à retravailler plus tard)
      | true, _ => return some (e1.getArg! 5, e1.getArg! 6, e2)
      | _, true => return some (e2.getArg! 5, e2.getArg! 6, e1)
      | _, _ => return none
  else
    return none

#check inferType


def toTrg (e : Expr × Expr × Expr) : MetaM (triangle String) := do
  let f ← ppExpr e.1
  let g ←  ppExpr e.2.1
  let h ←  ppExpr e.2.2

  return ⟨s!"{f}", s!"{g}", s!"{h}"⟩

def find_triangles_totrig (l : List (triangle String)) (e: Expr) : MetaM <|List (triangle String) := do
  match ← is_triangle ( ← inferType e) with
    | some (f , g, h) =>  return  ( ← toTrg (f, g, h)) :: l
    | none =>  return l

def find_triangles (l : List (Expr × Expr × Expr)) (e: Expr) : MetaM <|List (Expr × Expr × Expr) := do
  match ← is_triangle ( ← inferType e) with
    | some (f , g, h) =>
      logInfo m!"one triangle is {f} ≫ {g} = {h}"
      return  (f, g, h) :: l
    | none =>  return l

elab "find_triangles" : tactic => withMainContext do
  let hyp ← getLocalHyps
  let list_triangles :=  Array.foldlM (find_triangles) [] hyp
  logInfo m!" the triangles are { ← list_triangles}"


#check elabTerm

example : (c ≫ d) ≫ e = b ≫ e := by

  match_eq
  sorry


--def andThen : Expr → Expr → Expr :=
--  fun e => fun f => .app (.app (.const `CategoryStruct.comp []) e) f--probablement faux et à corriger plus tard



elab "GetPath" : tactic => withMainContext do
  let hyp ← getLocalHyps
  let list_triangles :=  Array.foldlM (find_triangles_totrig) [] hyp
  let list_hom ← ← match_eq (← getMainTarget)
  let l1 ←  (list_hom.1.mapM ppExpr : MetaM (List Format))
  let l1 := (l1.map (fun e => s!"{e}"))
  let res ←  CommDiag String ( ← list_triangles) l1

  --let rs ← (res.mapM ppString : MetaM (List Format))
  let l1 ←  (list_hom.1.mapM ppExpr : MetaM (List Format))
  let l2 ← (list_hom.2.mapM ppExpr : MetaM (List Format))
  logInfo m!" the old path is { l1} the new path is { res} and the goal is { l2}"



lemma test (h1 : c ≫ d = b) (h2 : b ≫ e = a ≫ g) (h3 : d ≫ e = f ≫ h) (h4 : g ≫ i = j) (h5 : h ≫ i = k) (h6 : f ≫ k = m ) (h7 : m ≫ l = n) : a ≫ j ≫ l = c ≫ n:= by
  match_eq
  find_triangles

  GetPath


  rw [←  h7, ← h6, ← h5, ← Category.assoc f h i, ←  h3, ← h4, ← Category.assoc a _ l, ← Category.assoc a g i,  ← h2, ← h1]

  repeat rw [Category.assoc]

macro "rw_assoc" f:term " et" g:term "et" h:term : tactic => do
  `(tactic| repeat (first | rw [ ← Category.assoc $f $g, $h:term ] | rw [ Category.assoc] ))

lemma test4 (h1 : c ≫ d = b) : c ≫ d ≫ e = b ≫ e:= by
  --rw [←  Category.assoc c d]
  rw_assoc c et d et h1



variable (a : A ⟶ B) (b : A ⟶ C) (c : B ⟶ C) (d : B ⟶ D) (e : D ⟶ C) (f : C ⟶ E) (g : D ⟶ E) (h : E ⟶ F) (i : D ⟶ F) (j : D ⟶ G) (k : F ⟶ G)

lemma test2 (h1 : a ≫ c = b ) (h2 : d ≫ e = c) (h3 : e ≫ f = g) (h4 : g ≫ h = i) (h5 : i ≫ k = j) : a ≫  d ≫ j = b ≫ f ≫ h ≫ k := by

  GetPath

  rw [← h5, ← h4, ← h3]
  slice_lhs 2 3 =>
    rw [h2]

  slice_lhs 1 2 =>
    rw [h1]
  repeat rw [Category.assoc]

variable (a : A ⟶ B) (b : B ⟶ D) (c : C ⟶ D) (d: A ⟶ C) (e: C ⟶ B)

lemma test3 (h1 : d ≫ e = a) (h2 : e ≫ b = c): a ≫ b = d ≫ c := by

  GetPath
  sorry



#check (apply : TacticM Unit)








--  sorry
