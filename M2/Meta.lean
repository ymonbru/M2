import Lean
import Mathlib.Tactic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Tactic.CategoryTheory.Slice
import M2.Comm_rw

open CategoryTheory Lean Meta Elab Tactic


variable (Cat : Type ) [Category Cat]

variable (A B C D E F G H : Cat) (a : A ⟶ D) (b : A ⟶ C) (c : A ⟶ B) (d : B ⟶ C) (e : C ⟶ E) (f : B ⟶ F) (h : F ⟶ E) (i : E ⟶ G) (j : D ⟶ G) (k : F ⟶ G) (l : G ⟶ H) (m : B ⟶ G) (n : B ⟶ H)



partial def match_comp (e : Expr) : MetaM <|(List Expr) := do
  if e.isAppOf ``CategoryStruct.comp then
    return (← match_comp (e.getArg! 5)) ++ (← match_comp (e.getArg! 6)) -- probablement pas optimal du tout
  else
    return [e]
--termination_by e
--decreasing_by
  --ça devrait se faire tout seul non?
--  · sorry
--  · sorry

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

partial def compLength (e : Expr) : MetaM Nat := do
  if e.isAppOf ``CategoryStruct.comp then
    return (← compLength (e.getArg! 5)) + (← compLength (e.getArg! 6)) + 1
  else
    return 0

def eqLength (e : Expr) : MetaM Nat := do
  let e ← whnf e
  if e.isAppOf ``Eq then
    return max (← compLength (e.getArg! 1)) (← compLength (e.getArg! 2))
  else
    return 0

def is_triangle (e:Expr) : MetaM <| Option (Expr × Expr × Expr ⊕ Expr × Expr × Expr × Expr × Expr × Expr) := do
  --let e ← whnf e
  if e.isAppOf ``Eq then
    let e1 := e.getArg! 1
    let e2 := e.getArg! 2
    match e1.isAppOf ``CategoryStruct.comp , e2.isAppOf ``CategoryStruct.comp with
      | true, true => return some <| .inr (e1.getArg! 5, e1.getArg! 6, e2, e2.getArg! 5, e2.getArg! 6, e1)--a square
      | true, _ => return some <| .inl (e1.getArg! 5, e1.getArg! 6, e2)
      | _, true => return some <| .inl (e2.getArg! 5, e2.getArg! 6, e1)
      | _, _ => return none
  else
    return none


#check inferType


def toTrg (e : Expr × Expr × Expr ) : MetaM (triangle):= do
  return ⟨e.1 ,e.2.1 ,e.2.2, e.1⟩--changer le e.1 à la fin

def find_triangles_totrig (l : List triangle ) (e: Expr) : MetaM <|List triangle := do
  match ← is_triangle ( ← inferType e) with
    | some <| .inl (f , g, h) =>  return  ( ← toTrg (f, g, h)) :: l
    | some <| .inr (f, g, hi, h, i, fg) => return (← toTrg (f, g, hi)) :: (← toTrg (h, i, fg)):: l
    | none =>  return l

def find_triangles (l : List (Expr × Expr × Expr)) (e: Expr) : MetaM <|List (Expr × Expr × Expr) := do
  match ← is_triangle ( ← inferType e) with
    | some <| .inl (f , g, h) =>
      logInfo m!"one triangle is {f} ≫ {g} = {h}"
      return  (f, g, h) :: l
    | some <| .inr (f, g, hi, h, i, fg) =>
      logInfo m!" one square is {f} ≫ {g} = {h} ≫ {i}"
      return (f, g, hi) :: (h, i, fg):: l
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
  let res ←  CommDiag  ( ← list_triangles) list_hom.1

  evalTactic $ ← `(tactic| repeat rw [Category.assoc])

  let l1 ←  (list_hom.1.mapM ppExpr : MetaM (List Format))
  let l2 ← (list_hom.2.mapM ppExpr : MetaM (List Format))
  logInfo m!" the old path is { l1} the new path is { res} and the goal is { l2}"



lemma test (h1 : c ≫ d = b) (h2 : b ≫ e = a ≫ g) (h3 : d ≫ e = f ≫ h) (h4 : g ≫ i = j) (h5 : h ≫ i = k) (h6 : f ≫ k = m ) (h7 : m ≫ l = n) : a ≫ j ≫ l = c ≫ n:= by
  match_eq
  find_triangles
  GetPath

  rw [←  h7, ← h6, ← h5, ← Category.assoc f h i, ←  h3, ← h4, ← Category.assoc a _ l, ← Category.assoc a g i,  ← h2, ← h1]
  repeat rw [Category.assoc]

macro "slice_lhs_aux" a:num "et " b:num "avec" h:term : tactic =>
  `(tactic| slice_lhs $a $b => rw [ ($h)])

macro "slice_rhs_aux" a:num "et " b:num "avec" h:term : tactic =>
  `(tactic| slice_rhs $a $b => rw [ ($h)])

elab "rw_assoc" h:term : tactic => withMainContext do
  let n ← eqLength (← getMainTarget)
  logInfo m!"{n}"
  let s0 ← saveState
  for j in [0:n] do
    let s ← saveState
    try
      let jLit := Syntax.mkNumLit <| toString j
      let jLitSucc := Syntax.mkNumLit <| toString (j+1)
      evalTactic $ ← `(tactic |  slice_lhs_aux $jLit et $jLitSucc avec $h)
      return
    catch _ =>
      restoreState s

    try
      let jLit := Syntax.mkNumLit <| toString j
      let jLitSucc := Syntax.mkNumLit <| toString (j+1)
      evalTactic $ ← `(tactic |  slice_rhs_aux $jLit et $jLitSucc avec $h)
      return
    catch _ =>
      restoreState s
  restoreState s0
  throwError "ça ne marche pas encore"



variable (a : A ⟶ B) (b : A ⟶ C) (c : B ⟶ C) (d : B ⟶ D) (e : D ⟶ C) (f : C ⟶ E) (g : D ⟶ E) (h : E ⟶ F) (i : D ⟶ F) (j : D ⟶ G) (k : F ⟶ G)

lemma test2 (h1 : a ≫ c = b ) (h2 : d ≫ e = c) (h3 : e ≫ f = g) (h4 : g ≫ h = i) (h5 : i ≫ k = j) : a ≫  d ≫ j = b ≫ f ≫ h ≫ k := by

  GetPath

  rw [← h5, ← h4, ← h3]
  rw_assoc h2
  rw_assoc h1
  repeat rw [Category.assoc]


#check Eq.symm

variable (a : A ⟶ B) (b : B ⟶ D) (c : C ⟶ D) (d: A ⟶ C) (e: C ⟶ B)

lemma test3 (h1 : d ≫ e = a) (h2 : e ≫ b = c): a ≫ b = d ≫ c := by

  GetPath
  sorry



#check (apply : TacticM Unit)








--  sorry
