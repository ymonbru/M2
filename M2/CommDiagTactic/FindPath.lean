import Lean
import Mathlib.Tactic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Tactic.CategoryTheory.Slice
--import M2.CommDiagTactic.Comm_rw
import M2.CommDiagTactic.BFS
import M2.CommDiagTactic.split_square
import M2.CommDiagTactic.IsUselessTactic
--import Egg

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

/-honteusement volé sur zulip-/
def mkTacticSeqAppend (ts : TSyntax `Lean.Parser.Tactic.tacticSeq) (t : TSyntax `tactic) : TermElabM (TSyntax `Lean.Parser.Tactic.tacticSeq) :=
  match ts with
  -- this patern is not used in the code but it is in the original code
  --| `(tacticSeq| { $[$tacs:tactic]* }) =>
  --  `(tacticSeq| { $[$(tacs.push t)]* })
  | `(tacticSeq| $[$tacs:tactic]*) =>
    `(tacticSeq| $[$(tacs.push t)]*)
  | _ => throwError "unknown syntax"


def combineTacticList (todo : List <| TSyntax `tactic) : TacticM <| TSyntax `Lean.Parser.Tactic.tacticSeq := withMainContext do
  match todo with
    | [] => `(tacticSeq| skip)
    | tac :: [] => `(tacticSeq| $tac:tactic)
    | tac :: todoQ =>
      let tacQ ← combineTacticList todoQ
      mkTacticSeqAppend tacQ tac

      --`(tacticSeq|
      --$tac
      --($tacQ))

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
def find_triangles_totrig (l : List <| Expr × Expr × Expr × Bool × Expr ) (e: Expr) : MetaM <|List <| Expr × Expr × Expr × Bool × Expr := do
  match ← is_triangle ( ← inferType e) with
    | some <| (f , g, h, b) =>  return (f, g, h, b, e)  :: l
    | none =>  return l


--def find (names : List <| Nat × Expr) (lHom: List Expr) : MetaM <| List <| Option Nat := sorry

def nameOne (names : List (Nat × Expr)) (nextN : Nat) (hom : Expr) : MetaM <| Nat × Nat × List (Nat × Expr) := do
  let nh ← names.findM? (fun (_, hom2) => isDefEq hom hom2)
  match nh with
    | none => return (nextN + 1, nextN, (nextN, hom) :: names)
    | some (n, _) => return (nextN, n, names)

def nameList (names : List (Nat × Expr)) (nextN : Nat) (lHom : List Expr) : MetaM <| Nat × List (Nat × Expr) × List Nat := match lHom with
  | [] => return (nextN, names, [])
  | h :: q => do
    let (nextN, n, names) ← nameOne names nextN h
    let (nextN, names, l) ← nameList names nextN q
    return (nextN, names, n :: l)

def step (names : List (Nat × Expr)) (nextN : Nat) (t : Expr × Expr × Expr × Bool × Expr) : MetaM <| Nat × (List (Nat × Expr)) × triangle := do
  let (f, g, h, b, e) := t
  let (nextN, nf, names) ← nameOne names nextN f
  let (nextN, ng, names) ← nameOne names nextN g
  let (nextN, nh, names) ← nameOne names nextN h

  let tTrig := ⟨nf, ng, nh, b, e⟩
  return (nextN, names, tTrig)




def nameInTriangle ( l : List <| Expr × Expr × Expr × Bool × Expr) : MetaM <| Nat × (List (Nat × Expr)) × (List triangle) :=
  match l with
    | [] => return (1, [], [])-- it's one to have 0 as an error value
    | t :: q => do
      let (nextN, names, tIdList) ← nameInTriangle q
      let (newNextN, newNames, tId) ← step names nextN t
      return (newNextN, newNames, tId :: tIdList)

/-- try to close a goal correct up to associativity-/
macro "repeat_assoc" : tactic => `(tactic| first |rfl | repeat rw [Category.assoc] | skip)


/-- Split all the square if needed then find the triangles and use the algo CommDiag to solve the goal-/
elab "findPath" : tactic => withMainContext do

  evalTactic $ ← `(tactic| split_square)

  withMainContext do
  let hyp ← getLocalHyps
  let list_triangles := Array.foldlM (find_triangles_totrig) [] hyp
  let (nextN, names, list_triangles) ← nameInTriangle (← list_triangles)

  match ← match_eq (← getMainTarget) with
    | none => return
    | some list_hom =>
      let (nextN, names, lh1) ←  nameList names nextN list_hom.1
      let (_, _, lh2) ← nameList names nextN list_hom.2
    --logInfo m!"{list_hom.1} et  {list_hom.2}"
      let TODO ←  findPathBFS  [] list_triangles lh1 lh2

    --let assoc←
      evalTacticList TODO.reverse
      evalTactic $ ← `(tactic| repeat_assoc)


def SuggestPath (stx : Syntax) : TacticM Unit := withMainContext do
  let split_square  ← `(tactic| split_square)
  let useless_split_square? ← IsUseless? (← getMainTarget) split_square
  let TODO := if useless_split_square? then [] else [split_square]

  --no need to compute it if is useless
  if not useless_split_square? then evalTactic $ split_square

  withMainContext do
  let hyp ← getLocalHyps
  let list_triangles :=  Array.foldlM (find_triangles_totrig) [] hyp
  let (nextN, names, list_triangles) ← nameInTriangle (← list_triangles)

  match ← match_eq (← getMainTarget) with
    | none => return
    | some list_hom =>
      let (nextN, names, lh1) ←  nameList names nextN list_hom.1
      let (_, _, lh2) ← nameList names nextN list_hom.2
    --logInfo m!"{list_hom.1} et  {list_hom.2}"
      let TODO ←  findPathBFS  TODO list_triangles lh1 lh2


      let s0 ← saveState
      try
        let partialTODO ← combineTacticList TODO
        evalTactic $ partialTODO
        let repeat_assoc ← `(tactic| repeat_assoc)
        let useless_repeat_assoc? ← IsUseless? (← getMainTarget) repeat_assoc

        restoreState s0

        let TODO := if not useless_repeat_assoc? then
          repeat_assoc :: TODO
          else TODO

      /-let TODO := if useless_split_square? then TODO else split_square :: TODO-/

        let TODO ← combineTacticList TODO
        TryThis.addSuggestion stx TODO
      catch _ => -- it closes the goal then repaet assoc is not needed
        --let TODO := if useless_split_square? then TODO else TODO ++ [split_square] -- c'est pas fou mais pas pire que les reverse que j'enlève avec la version de concatenantion de tacticSeq de zulip
        let TODO ← combineTacticList TODO
        TryThis.addSuggestion stx TODO




syntax (name := FindPathStx) "findPath?" : tactic

elab_rules : tactic
  | `(tactic| findPath?%$tk) => SuggestPath tk


 /- Exemples -/
set_option trace.profiler true


variable (Cat : Type ) [Category Cat]

variable (A B C D E F G H : Cat) (a : A ⟶ D) (b : A ⟶ C) (c : A ⟶ B) (d : B ⟶ C) (e : C ⟶ E) (f : B ⟶ F) (h : F ⟶ E) (i : E ⟶ G) (j : D ⟶ G) (k : F ⟶ G) (l : G ⟶ H) (m : B ⟶ G) (n : B ⟶ H)

lemma test (h1 : c ≫ d = b) (h2 : b ≫ e = a ≫ g) (h3 : d ≫ e = f ≫ h) (h4 : g ≫ i = j) (h5 : h ≫ i = k) (h6 : f ≫ k = m ) (h7 : m ≫ l = n) : a ≫ j ≫ l = c ≫ n:= by
  findPath

variable (a : A ⟶ B) (b : A ⟶ C) (c : B ⟶ C) (d : B ⟶ D) (e : D ⟶ C) (f : C ⟶ E) (g : D ⟶ E) (h : E ⟶ F) (i : D ⟶ F) (j : D ⟶ G) (k : F ⟶ G) (l : E ⟶ G)

-- (h6 : h ≫ k = l )
lemma test23  (h1 : a ≫ c  = b) (h2 : d ≫ e = c) (h3 : e ≫ f = g) (h4 : g ≫ h = i) (h5 :  i ≫ k = j ) : a ≫  d ≫ j = b ≫ f ≫ h ≫ k := by
  findPath

variable (a : A ⟶ B) (b : B ⟶ D) (c : C ⟶ D) (d: A ⟶ C) (e: C ⟶ B)

lemma test3 (h1 : d ≫ e = a) (h2 : e ≫ b = c): a ≫ b = d ≫ c := by
  findPath


variable (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ D) (d: D ⟶ C) (e: A ⟶ E) (f: E ⟶ C) (g: A ⟶ C)


lemma test4 (h1 : a ≫ b = g)  (h2 : c ≫ d = g) (h3: e ≫ f = g) : a ≫ b = c ≫ d := by
  findPath

variable (a:A ⟶ B) (b: B ⟶ C) (y : A ⟶ C) (c d : C ⟶ D)

lemma test567 (h1: a≫ b = y) : y ≫ c= y ≫ d := by

  sorry



variable (a ap: A ⟶ B) (b bp: B ⟶ C ) (x xp : A ⟶ C) (y yp : B ⟶ D) (c cp d  : C ⟶ D)

lemma FinDesHaricot (h1 : a ≫ b = x) (h2 : ap ≫ bp =x) (h3: b ≫ c =y) (h4 : bp ≫ cp = yp) (h5 : b ≫ d = y) (h6 : bp ≫ d = yp ) : a ≫ b ≫ c = ap ≫ bp ≫ cp := by
  findPath?

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
  --hint
  findPath?

  rw_assoc h2
  findPath

--https://q.uiver.app/#q=WzAsOSxbMCw0LCJBIl0sWzIsNCwiQiJdLFszLDYsIkMiXSxbMywzLCJEIl0sWzQsMiwiRSJdLFs2LDIsIkYiXSxbNyw0LCJHIl0sWzcsMSwiSCJdLFs4LDAsIkkiXSxbMCwxLCJhIiwxXSxbMSwyLCJ4IiwxXSxbMiwzLCJiIiwxXSxbMyw0LCJkIiwxXSxbMCwyLCJ5IiwxXSxbMSwzLCJjIiwxXSxbMCwzLCJlIiwxXSxbMCw0LCJmIiwxXSxbMiw0LCJnIiwxXSxbNCw1LCJhJyIsMV0sWzQsNiwieSciLDFdLFs1LDYsIngnIiwxXSxbNiw3LCJiJyIsMV0sWzUsNywiYyciLDFdLFs0LDcsImUnIiwxXSxbNyw4LCJkJyIsMV0sWzQsOCwiZiciLDFdLFs2LDgsImcnIiwxXV0=

lemma test10 (h1 : a ≫ x = y) (h2 : x ≫ b = c) (h3 : a ≫ c = e)
(h4 : e ≫ d = f) (h5 : y ≫ g = f) : a ≫ x ≫ b ≫ d = a ≫ x ≫ g := by
  findPath

variable (A B C D E F G : Cat)
variable (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (d : D ⟶ E) (e : E ⟶ F) (x: A ⟶ C) (xp: A ⟶ G) (y : C ⟶ E) (yp : G ⟶ F) (u : B ⟶ G) (v : G ⟶ E)

-- si on retire h1 (qui n'est pas utilisé) ça marche
lemma test11 (h1 : a ≫ b = x) (h2 : b ≫ y = u ≫ v) (h3 : y = c ≫ d) (h4 : a ≫ u = xp) (h5 : v ≫ e = yp) : a ≫ b ≫ c ≫ d ≫ e = a ≫ u ≫ yp := by
  findPath?

  rw_assoc h3
  rw_assoc_rhs h4
  conv => rhs; rw [← h5]
  rw_assoc_lhs h2.map_eq_left
  conv => lhs; rw [← h2.map_eq_right]
  rw_assoc_lhs h4
  repeat_assoc
--https://q.uiver.app/#q=WzAsMTUsWzAsMSwiQSJdLFsyLDEsIkIiXSxbMywwLCJDIl0sWzUsMCwiRCJdLFs0LDEsIkUiXSxbNSwyLCJGIl0sWzMsMiwiRyJdLFs3LDAsImFiY2RlIl0sWzksMCwiYWJ5ZSJdLFs3LDIsInhjZGUiXSxbOSwyLCJ4eWUiXSxbMTEsMCwiYXV2ZSJdLFsxMSwyLCJ4J3ZlIl0sWzEzLDIsIngneSciXSxbMTMsMCwiYXV5JyJdLFswLDEsImEiLDFdLFsxLDIsImIiLDFdLFswLDIsIngiLDFdLFsyLDMsImMiLDFdLFszLDQsImQiLDFdLFsyLDQsInkiLDFdLFs0LDUsImUiLDFdLFsxLDYsInUiLDFdLFs2LDQsInYiLDFdLFswLDYsIngnIiwxXSxbNiw1LCJ5JyIsMV0sWzcsOCwiMyIsMV0sWzcsOSwiMSIsMV0sWzksMTAsIjMiLDFdLFs4LDEwLCIxIiwxXSxbOCwxMSwiMiIsMV0sWzExLDEyLCI0IiwxXSxbMTIsMTMsIjUiLDFdLFsxMSwxNCwiNSIsMV0sWzE0LDEzLCI0IiwxXV0=
