import Lean
import Mathlib.Tactic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Tactic.CategoryTheory.Slice
import M2.Comm_rw
import M2.split_square

open CategoryTheory Lean Meta Elab Tactic

def evalTacticList (todo: List <| TSyntax `tactic) : TacticM Unit := withMainContext do
  --logInfo m!"{← getMainTarget}, {todo.length}"
  match todo with
    |[] => return ()
    | tac :: [] =>
      -- to avoid trying a tactic when the goal is closed.
      evalTactic $ tac

    | tac :: todoQ =>
      evalTactic $ tac
      evalTacticList todoQ

def combineTacticList (todo : List <| TSyntax `tactic) : TacticM <| TSyntax `tactic := withMainContext do
  match todo with
    | [] => return `(tactic| skip)
    | tac :: [] => return tac
    | tac :: todoQ =>
      let tacQ ← combineTacticList todoQ
      return `(tactic| $tac; $tacQ)

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


/- build a data structure triangle (from M2.Comm_rw) that represent the composition h : e.1 ≫ e.2.1 =e.2.2
def toTrg (e : Expr × Expr × Expr ) (h : Expr) : MetaM (triangle):= do
  return ⟨e.1 ,e.2.1 ,e.2.2, true, h⟩--/

/-- a step in FindPath that add to the list the triangle coresponding to e if it represents a triangle  -/
def find_triangles_totrig (l : List triangle ) (e: Expr) : MetaM <|List triangle := do
  match ← is_triangle ( ← inferType e) with
    | some <| (f , g, h, b) =>  return ⟨f, g, h, b, e⟩  :: l
    | none =>  return l


/-- Split all the square if needed then find the triangles and use the algo CommDiag to solve the goal-/
elab "findPath" : tactic => withMainContext do

  evalTactic $ ← `(tactic| split_square)

  withMainContext do
  let hyp ← getLocalHyps
  let list_triangles :=  Array.foldlM (find_triangles_totrig) [] hyp
  match ← match_eq (← getMainTarget) with
    | none => return
    | some list_hom =>
    --logInfo m!"{list_hom.1} et  {list_hom.2}"
    let TODO ←  FindPath  ( ← list_triangles)  list_hom.1 list_hom.2

    evalTacticList TODO.reverse
    evalTactic $ ← `(tactic| first | repeat rw [Category.assoc] | skip)




def SuggestPath (stx : Syntax) : TacticM Unit := withMainContext do
  evalTactic $ ← `(tactic| split_square)

  withMainContext do
  let hyp ← getLocalHyps
  let list_triangles :=  Array.foldlM (find_triangles_totrig) [] hyp
  logInfo m!"{(← list_triangles).length}"
  match ← match_eq (← getMainTarget) with
    | none => return
    | some list_hom =>
    --logInfo m!"{list_hom.1} et  {list_hom.2}"
    let TODO ←  FindPath  ( ← list_triangles)  list_hom.1 list_hom.2

    let TODO := ( ← `(tactic| first | repeat rw [Category.assoc] | skip)) :: TODO
    let TODO:= TODO.reverse

    let results ← TODO.mapA fun t : TSyntax `tactic => do
      return  ← Mathlib.Tactic.Hint.suggestion t

    let results := results.toArray

    let tac1 ← `(tactic| rfl)
    let tac2 ← `(tactic| split_square)

    let combinedTac ← `(tactic| $tac2; $tac2; $tac2)
    let machin ← `(tactic| $tac1;  seq:($combinedTac))



    TryThis.addSuggestion stx machin

    TryThis.addSuggestions stx results



syntax (name := FindPathStx) "findPath?" : tactic

elab_rules : tactic
  | `(tactic| findPath?%$tk) => SuggestPath tk


 /- Exemples -/
set_option trace.profiler true


variable (Cat : Type ) [Category Cat]

variable (A B C D E F G H : Cat) (a : A ⟶ D) (b : A ⟶ C) (c : A ⟶ B) (d : B ⟶ C) (e : C ⟶ E) (f : B ⟶ F) (h : F ⟶ E) (i : E ⟶ G) (j : D ⟶ G) (k : F ⟶ G) (l : G ⟶ H) (m : B ⟶ G) (n : B ⟶ H)

lemma test (h1 : c ≫ d = b) (h2 : b ≫ e = a ≫ g) (h3 : d ≫ e = f ≫ h) (h4 : g ≫ i = j) (h5 : h ≫ i = k) (h6 : f ≫ k = m ) (h7 : m ≫ l = n) : a ≫ j ≫ l = c ≫ n:= by
  --rw [← h7, ← h6, ← h5]
  aesopTactic?


  findPath?

  /-
  rw [← h7, ← h6, ← h5,]
  rw_assoc2 h3.map_eq_right
  rw [← h3.map_eq_left]
  rw_assoc2 h1
  rw_assoc2 h2.map_eq_left
  rw[← h2.map_eq_right]
  rw_assoc h4-/
  --rw [←  h7, ← h6, ← h5, ← Category.assoc f h i, ←  h3, ← h4, ← Category.assoc a _ l, ← Category.assoc a g i,  ← h2, ← h1]
  --repeat rw [Category.assoc]

variable (a : A ⟶ B) (b : A ⟶ C) (c : B ⟶ C) (d : B ⟶ D) (e : D ⟶ C) (f : C ⟶ E) (g : D ⟶ E) (h : E ⟶ F) (i : D ⟶ F) (j : D ⟶ G) (k : F ⟶ G) (l : E ⟶ G)

-- (h6 : h ≫ k = l )
lemma test23  (h1 : a ≫ c  = b) (h2 : d ≫ e = c) (h3 : e ≫ f = g) (h4 : g ≫ h = i) (h5 :  i ≫ k = j ) : a ≫  d ≫ j = b ≫ f ≫ h ≫ k := by
  findPath
  --FindPath
  --rw [ ← h5, ← h4, ← h3]
  --rw_assoc h2
  --rw_assoc h1
  --repeat rw [Category.assoc]

variable (a : A ⟶ B) (b : B ⟶ D) (c : C ⟶ D) (d: A ⟶ C) (e: C ⟶ B)

lemma test3 (h1 : d ≫ e = a) (h2 : e ≫ b = c): a ≫ b = d ≫ c := by
  --rw [← h1]
  --rw_assoc2 h2
  findPath


variable (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ D) (d: D ⟶ C) (e: A ⟶ E) (f: E ⟶ C) (g: A ⟶ C)


lemma test4 (h1 : a ≫ b = g)  (h2 : c ≫ d = g) (h3: e ≫ f = g) : a ≫ b = c ≫ d := by
  findPath

variable (a:A⟶  B) (b: B⟶  C) (y : A⟶ C) (c d : C⟶  D)

lemma test567 (h1: a≫ b = y) : y ≫ c= y ≫ d := by
  findPath
  --rw [← h1]
  conv => lhs ; rw [← h1]
  sorry



variable (a ap: A ⟶ B) (b bp: B ⟶ C ) (x xp : A ⟶ C) (y yp : B ⟶ D) (c cp d  : C ⟶ D)

lemma FinDesHaricot (h1 : a ≫ b = x) (h2 : ap ≫ bp =x) (h3: b ≫ c =y) (h4 : bp ≫ cp = yp) (h5 : b ≫ d = y) (h6 : bp ≫ d = yp ) : a ≫ b ≫ c = ap ≫ bp ≫ cp := by
  findPath

  rw [h3, h4, ← h6, ← h5]
  rw_assoc h1
  rw_assoc h2


/-https://q.uiver.app/#q=WzAsNCxbMCwwLCJBIl0sWzIsMCwiQiJdLFsyLDIsIkMiXSxbNCwwLCJEIl0sWzAsMSwiYSIsMV0sWzEsMiwiYiIsMV0sWzAsMSwiYSciLDEseyJjdXJ2ZSI6LTJ9XSxbMSwyLCJiJyIsMSx7ImN1cnZlIjotMn1dLFswLDIsIngiLDEseyJjdXJ2ZSI6Mn1dLFswLDIsIngnIiwxLHsiY3VydmUiOjV9XSxbMSwzLCJ5IiwxXSxbMSwzLCJ5JyIsMSx7ImN1cnZlIjotMn1dLFsyLDMsImQiLDFdLFsyLDMsImMiLDEseyJjdXJ2ZSI6Mn1dLFsyLDMsImMnIiwxLHsiY3VydmUiOjV9XV0=-/





lemma test5 (h1 : a ≫ b = g)  (h2 : c ≫ d = g) (h3: e ≫ f = g) : a ≫ b = a ≫ b := by
  findPath

lemma test6  : a ≫ b = a ≫ b := by
  findPath

variable (a: A ⟶ B) (b : A ⟶ C) (c: B ⟶ C) (d e x: B⟶ D) (f: D ⟶ C) (g: D ⟶ E) (h i y : C ⟶ E)

lemma test7  (h1 : b = a ≫ c) (h2 : f ≫ h = g) (h3 : f ≫ i = g) (h4 : d ≫ f = c)
(h5 : e ≫ f = c ) (h6 : x ≫ f = c) (h7 : f ≫ y = g): a ≫ c ≫ y= a ≫ c ≫ i := by
  findPath


variable (A B C D : Cat)
variable (x : A ⟶ B) (y u : B ⟶ C) (z : A ⟶ C) (b : B ⟶ D) (a : C ⟶ D)

lemma test8 (h1 : x ≫ y = z) (h2: b = u ≫ a) (h3 : y ≫ a = b) (h4 : z = x ≫ u): x ≫ y ≫ a = x ≫ u ≫ a := by
  findPath

variable (A B C D E F G H I : Cat)
variable (x : B ⟶ C) (y : A ⟶ C) (a : A ⟶ B) (b : C ⟶ D) (c : B ⟶ D) (d : D ⟶ E) (e : A ⟶ D) (f : A ⟶ E) (g : C ⟶ E) (xp : F ⟶ G) (yp : E ⟶ G) (ap : E ⟶ F) (bp : G ⟶ H) (cp : F ⟶ H) (dp : H ⟶ I) (ep : E ⟶ H) (fp : E ⟶ I) (gp : G ⟶ I)

lemma test9 (h1 : a ≫ x = y) (h2 : x ≫ b = c) (h3 : a ≫ c = e)
(h4 : e ≫ d = f) (h5 : y ≫ g = f) (h6 : ap ≫ xp = yp) (h7 : xp ≫ bp = cp) (h8 : ap ≫ cp = ep) (h9 : ep ≫ dp = fp) (h10 : yp ≫ gp = fp) : a ≫ x ≫ b ≫ d ≫ ap ≫ xp ≫ gp = a ≫ x ≫ g ≫ ap ≫ xp ≫ bp ≫ dp := by
  hint
  findPath

  rw_assoc h2
  findPath

--https://q.uiver.app/#q=WzAsOSxbMCw0LCJBIl0sWzIsNCwiQiJdLFszLDYsIkMiXSxbMywzLCJEIl0sWzQsMiwiRSJdLFs2LDIsIkYiXSxbNyw0LCJHIl0sWzcsMSwiSCJdLFs4LDAsIkkiXSxbMCwxLCJhIiwxXSxbMSwyLCJ4IiwxXSxbMiwzLCJiIiwxXSxbMyw0LCJkIiwxXSxbMCwyLCJ5IiwxXSxbMSwzLCJjIiwxXSxbMCwzLCJlIiwxXSxbMCw0LCJmIiwxXSxbMiw0LCJnIiwxXSxbNCw1LCJhJyIsMV0sWzQsNiwieSciLDFdLFs1LDYsIngnIiwxXSxbNiw3LCJiJyIsMV0sWzUsNywiYyciLDFdLFs0LDcsImUnIiwxXSxbNyw4LCJkJyIsMV0sWzQsOCwiZiciLDFdLFs2LDgsImcnIiwxXV0=

lemma test10 (h1 : a ≫ x = y) (h2 : x ≫ b = c) (h3 : a ≫ c = e)
(h4 : e ≫ d = f) (h5 : y ≫ g = f) : a ≫ x ≫ b ≫ d = a ≫ x ≫ g := by
  findPath
