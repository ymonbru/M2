import Lean
import Mathlib.Tactic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Tactic.CategoryTheory.Slice
--import M2.CommDiagTactic.Comm_rw
import M2.CommDiagTactic.BFS
import M2.CommDiagTactic.split_square
import M2.CommDiagTactic.IsUselessTactic


/-TODO: improove the time (????) by dealing with square-/
open CategoryTheory Lean Meta Elab Tactic

/-- take a list of tactics and evaluate then-/
def evalTacticList (todo: List <| TSyntax `tactic) : TacticM Unit := withMainContext do
  match todo with
    |[] => return ()
    | tac :: [] =>
      -- to avoid trying a tactic when the goal is closed.
      evalTactic $ tac

    | tac :: todoQ =>
      evalTactic $ tac
      evalTacticList todoQ

/-- take a tacticSeq and add a nex tactic to it, stolen on zulip-/
def mkTacticSeqAppend (ts : TSyntax `Lean.Parser.Tactic.tacticSeq) (t : TSyntax `tactic) : TermElabM (TSyntax `Lean.Parser.Tactic.tacticSeq) :=
  match ts with
  -- this patern is not used in the code but it is in the original code
  --| `(tacticSeq| { $[$tacs:tactic]* }) =>
  --  `(tacticSeq| { $[$(tacs.push t)]* })
  | `(tacticSeq| $[$tacs:tactic]*) =>
    `(tacticSeq| $[$(tacs.push t)]*)
  | _ => throwError "unknown syntax"

/-- take a list of tactic and make it into a single taketic by using mkTacticSeqAppend-/
def combineTacticList (todo : List <| TSyntax `tactic) : TacticM <| TSyntax `Lean.Parser.Tactic.tacticSeq := withMainContext do
  match todo with
    | [] => `(tacticSeq| skip)
    | tac :: [] => `(tacticSeq| $tac:tactic)
    | tac :: todoQ =>
      let tacQ ← combineTacticList todoQ
      mkTacticSeqAppend tacQ tac

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

/-- check if the expression correspond to  a ≫ b = c or c = a ≫ b and gives the three morphisms involved -/
def is_triangle (e : Expr) : MetaM <| Option ( Expr × Expr × Expr × Bool) := do
  let e ← whnf e
  if e.isAppOf ``Eq then
    let e1 := e.getArg! 1
    let e2 := e.getArg! 2
    match e1.isAppOf ``CategoryStruct.comp , e2.isAppOf ``CategoryStruct.comp with
      | true, true => return none
      | true, _ => return (e1.getArg! 5, e1.getArg! 6, e2, true)
      | _, true => return (e2.getArg! 5, e2.getArg! 6, e1, false)
      | _, _ => return none
  else
    return none

/-- a step in FindPath that add to the list the triangle coresponding to e if it represents a triangle  -/
def find_triangles_totrig (l : List <| Expr × Expr × Expr × Bool × Expr ) (e: Expr) : MetaM <|List <| Expr × Expr × Expr × Bool × Expr := do
  match ← is_triangle ( ← inferType e) with
    | some <| (f , g, h, b) =>  return (f, g, h, b, e)  :: l
    | none =>  return l

/-- check if hom is registered in the list names, if yes gives back the number, if no add it to the list, and return the number of hom and the new next number to give-/
def nameOne (names : List (Nat × Expr)) (nextN : Nat) (hom : Expr) : MetaM <| Nat × Nat × List (Nat × Expr) := do
  let nh ← names.findM? (fun (_, hom2) => isDefEq hom hom2)
  match nh with
    | none => return (nextN + 1, nextN, (nextN, hom) :: names)
    | some (n, _) => return (nextN, n, names)

/-- add names to the lis lHom by using name One-/
def nameList (names : List (Nat × Expr)) (nextN : Nat) (lHom : List Expr) : MetaM <| Nat × List (Nat × Expr) × List Nat := match lHom with
  | [] => return (nextN, names, [])
  | h :: q => do
    let (nextN, n, names) ← nameOne names nextN h
    let (nextN, names, l) ← nameList names nextN q
    return (nextN, names, n :: l)

/-- add the names of a triangle to the list names by using nameOne -/
def stepNameInTriangle (names : List (Nat × Expr)) (nextN : Nat) (t : Expr × Expr × Expr × Bool × Expr) : MetaM <| Nat × (List (Nat × Expr)) × triangle Nat := do
  let (f, g, h, b, e) := t
  let (nextN, nf, names) ← nameOne names nextN f
  let (nextN, ng, names) ← nameOne names nextN g
  let (nextN, nh, names) ← nameOne names nextN h

  let tTrig := ⟨nf, ng, nh, b, e⟩
  return (nextN, names, tTrig)

/-- add the names of a list of triangles by iterating stepNamesInTriangle -/
def nameInTriangle ( l : List <| Expr × Expr × Expr × Bool × Expr) : MetaM <| Nat × (List (Nat × Expr)) × (List (triangle Nat)) :=
  match l with
    | [] => return (1, [], [])
    | t :: q => do
      let (nextN, names, tIdList) ← nameInTriangle q
      let (newNextN, newNames, tId) ← stepNameInTriangle names nextN t
      return (newNextN, newNames, tId :: tIdList)

/-- try to close a goal correct up to associativity-/
macro "repeat_assoc" : tactic => `(tactic| first |rfl | repeat rw [Category.assoc] | skip)


/-- Split all the square if needed then find the triangles and use the algo findPathBFS to solve the goal-/
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
      let TODO := (←  findPathBFS Nat list_triangles lh1 lh2).reverse

      evalTacticList TODO.reverse
      evalTactic $ ← `(tactic| repeat_assoc)

/-- Same thing as findPath, except that it gives the suggestion of the tactic to apply instead of evaluating them-/
def SuggestPath (stx : Syntax) : TacticM Unit := withMainContext do
  let split_square  ← `(tactic| split_square)
  let useless_split_square? ← IsUseless? (← getMainTarget) split_square

  --no need to compute the tactic does nothing
  -- the context is modified if needed to have the suggestions in the good context, and the tactic will be added to suggestion if needed.
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

      let TODO ←  findPathBFS Nat list_triangles lh1 lh2
      let TODO := if not useless_split_square? then
        (split_square :: TODO).reverse
      else
        TODO.reverse

      -- in order to know if repeat_assoc is needed in the final suggestion we need to try all the other tactitcs
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
        let TODO ← combineTacticList TODO
        TryThis.addSuggestion stx TODO
      catch _ =>
        --if there is an error, it's because the first tactics closes the goal: then repaet assoc is not needed
        let TODO ← combineTacticList TODO
        TryThis.addSuggestion stx TODO

/-- implementation of the tactic findPath?-/
syntax (name := FindPathStx) "findPath?" : tactic

elab_rules : tactic
  | `(tactic| findPath?%$tk) => SuggestPath tk
