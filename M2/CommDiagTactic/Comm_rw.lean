import Mathlib.Tactic
import Mathlib.Data.Nat.Defs
import Lean
import M2.CommDiagTactic.rw_assoc
/- Bon alors du coup dans ce fichier l'algo est correct mais est trop loin d'être complet...-/

open Lean Meta Elab Tactic
@[ext]
structure triangle where--f ≫ g = h
  f : Nat--id of f
  g : Nat
  h : Nat
  dir : Bool -- true if f ≫ g is on the letf side of the equation in the context
  proof : Expr
deriving Repr


/-- hom represent the sequence of morphisms, the algo try to rewrite the rule coresponding to the triangle t

The boolean is true if nothing is changed and false otherwise-/
def applyTriangle (t : triangle) (hom : List Nat ) : TacticM (Bool × List Nat) := withMainContext do
match hom with
  | [] => return (true, hom)
  | _ :: [] => return (true, hom)
  | a :: b :: homPrime =>
    if (a = t.f) ∧ (b = t.g) then

      --let proofTerm ← Term.exprToSyntax t.proof
      --evalTactic $ ← `(tactic| first | rw_assoc2 $proofTerm | skip  )

      --logInfo m!"the composition {← ppExpr t.f} ≫ {← ppExpr t.g} is replaced by {← ppExpr t.h}"

      return (false, t.h :: homPrime)
    else
      let (unchanged?, newHom) ←  applyTriangle t (b::homPrime)
      return (unchanged?, a::newHom)

/-- The algo try every rewriting rule of the list lt to the sequence of morphisms.

The boolean is true if nothing is changed and false otherwise-/
def applyListTriangles (lt : List triangle) ( lastUsed : Option triangle) (hom : List Nat) (tacticTODO: List <| TSyntax `tactic) (left : Bool): TacticM (Bool × List triangle × Option triangle × List Nat × (List <| TSyntax `tactic)) :=
  match lt with
    | [] => return (true, [], lastUsed, hom, tacticTODO)
    | t :: ltQ => do
      let (newbool, newlt, newLastUsed, newHom, newTacticTODO) ←  applyListTriangles ltQ lastUsed hom tacticTODO left
      let (b, nnewHom) ←  applyTriangle t newHom

      if b then
        return (newbool, t :: newlt, newLastUsed, newHom, newTacticTODO)
      else
        let proofTerm ← PrettyPrinter.delab t.proof
        let tac ←  if left then
          `(tactic| rw_assoc_lhs $proofTerm )
        else
          `(tactic| rw_assoc_rhs $proofTerm )

        return (false, newlt, some t , nnewHom, tac :: newTacticTODO)


/-- The algo try to expand the rule t in the sequence c (expanding means that if t: f ≫ g = h and h is in c then h is replaced by f≫ g).

The boolean is true if nothing is changed and false otherwise-/
def expandTriangle (ok : Bool) (t : triangle) (hom : List Nat ) : TacticM (Bool × List Nat ):= withMainContext do
  if not ok then return (false, hom)
  else  match hom with
    |[] => return (ok, hom)
    |a :: homQ =>
      if t.h = a then

      --let proofTerm ← Term.exprToSyntax t.proof
      --evalTactic $ ← `(tactic| first | rw [← $proofTerm] | rw [ ($proofTerm) ]| skip )

      -- rw term in both direction to avoid problem when the triangle is on the other direction in the context.
      --logInfo m!"the morphism {← ppExpr t.h} is replaced by the composition {← ppExpr t.f} ≫ {← ppExpr t.g}"

      return (false, t.f :: t.g :: homQ)
      else
        let (newok, newHom) ←  expandTriangle  ok t homQ
        return (newok, a :: newHom)

/-- The algo try to expand the one rule of lt (and stops when it's done) in the sequence hom .

The boolean is true if nothing is changed and false otherwise-/
def expandOneTriangle (lt : List triangle) (lastUsed : Option triangle) (hom : List Nat ) (tacticTODO: List <| TSyntax `tactic) (left : Bool): TacticM (Bool × Option triangle × List triangle × List Nat × (List <| TSyntax `tactic) ) := match lt with
  | []=> return (true, lastUsed, lt, hom, tacticTODO)
  | t :: ltQ => do
    let (b, newHom) ←  expandTriangle true t hom
    if b then
      let (expanded?, newLastUsed, newLt, nnewHom, newTacticTODO) ←  expandOneTriangle ltQ lastUsed newHom tacticTODO left
      return (expanded?, newLastUsed, t::newLt, nnewHom, newTacticTODO)
    else

      let proofTerm ← PrettyPrinter.delab t.proof

      let tac ← match left, t.dir with
        | true, true => `(tactic| conv => lhs; rw [← $proofTerm] )
        | true, false => `(tactic| conv => lhs; rw [($proofTerm)] )
        | false, true => `(tactic| conv => rhs; rw [← $proofTerm] )
        | false, false => `(tactic| conv => rhs; rw [($proofTerm)] )


      /-if left then
        `(tactic| conv => lhs; first | rw [($proofTerm)] | rw [← ($proofTerm)])
        else
        `(tactic| conv => rhs; first | rw [($proofTerm)] | rw [← ($proofTerm)])-/

      return (false, some t, ltQ, newHom, tac :: tacticTODO)


/-- Apply all the reduction rules that can be applied, rewrite one backwards and continue while something has changed.-/
partial def CommDiag (lt : List triangle) (lastUsed : Option triangle) (Hom : List Nat) (tacticTODO: List <| TSyntax `tactic) (left : Bool): TacticM <| List Nat × Option triangle × (List <| TSyntax `tactic) := do

  let (modif?aplt, newLt, newLastUsed, newHom, newTacticTODO) ←  applyListTriangles lt lastUsed Hom tacticTODO left
  let (modif?eot, nnewLastUsed, nnewLt, nnewHom, nnewTacticTODO) ←  expandOneTriangle newLt newLastUsed newHom newTacticTODO left

  if not modif?eot ∨ not modif?aplt then
    CommDiag nnewLt nnewLastUsed nnewHom nnewTacticTODO left
  else
    return (nnewHom, nnewLastUsed, nnewTacticTODO)

--The algo terminates because it continues while the length of lt is decreasing

def clear (usedT : triangle) (lt : List triangle) : MetaM <| List triangle :=
  match lt with
    | [] => return []
    | t :: q => do
      if ← isDefEq t.proof usedT.proof then
        clear usedT q-- in case the relation is present many times
      else
        return t :: (← clear usedT q)

/-def isFinished (hom homEnd : List Nat) : MetaM Bool :=
  match hom, homEnd with
  | [], [] => return true
  | h1 :: homQ, h2 :: homEndQ => do
    if ( h1 = h2) then
      isFinished homQ homEndQ
    else
      return false
  | _, _ => return false-/

partial def CommDiagWithRestart (lt : List triangle) (hom homEnd : List Nat) (TODO : List <| TSyntax `tactic) (left : Bool): TacticM <| List <| TSyntax `tactic := do
  if hom = homEnd then
    return  TODO
  else
    let (newHom, lastUsedTriangle, newTODO) ←  CommDiag lt none hom TODO left
      if not (newHom = homEnd) then
        --logInfo m!"START AGAIN"
        match lastUsedTriangle with
          | none => pure []
          | some t  =>
              let newLt ←  clear t lt
              CommDiagWithRestart newLt hom homEnd TODO left
      else
        return newTODO

partial def FindPath (dep : List <| TSyntax `tactic) (lt : List triangle) (hom homEnd : List Nat): TacticM <| List <| TSyntax `tactic := do
  match lt with
    |[] => return []
    | _ =>
    let TODO ← CommDiagWithRestart lt hom homEnd dep true
    match TODO with
      | [] =>
        --logInfo m!"Try to reduce the left hand side"
        let (newHomEnd, lastUsedTriangle, newTODO) ← CommDiag lt none homEnd dep false

        --logInfo m!"start again with the new end"
        let nnewTODO ← CommDiagWithRestart lt hom newHomEnd newTODO true
        match nnewTODO with
          |[] =>
            match lastUsedTriangle with
              | none => return []
              | some t =>
                let newLt ← clear t lt
                --logInfo m!"REAL Restart"
                FindPath dep newLt hom homEnd
          | _ => return nnewTODO

      | _ => return TODO




/- bien tenté mais ça ne marche pas super
partial def FindPath2 (lt : List triangle) (hom homEnd : List Expr) (lastUsedTriangle : Option triangle) (TODO : List <| TSyntax `tactic): TacticM <| List <| TSyntax `tactic := do
    logInfo m!"{hom} et {homEnd}"
    if not (← isFinished hom homEnd) then
        logInfo m!"START AGAIN and eliminate rules"
        match lastUsedTriangle with
          | none =>
            logInfo m!"FAIILLED"
            pure []
          | some t  =>
              let newLt ←  clear t lt
              let (newHom, newLastUsedTriangle, newTODO) ← CommDiag newLt none hom TODO
              FindPath2 newLt newHom homEnd newLastUsedTriangle newTODO

    else
      logInfo m!"work is done"
      return TODO


partial def FindPath3 (lt : List triangle) (hom homEnd : List Expr): TacticM <| List <| TSyntax `tactic :=  do
  logInfo m!"Start here"

  let (newHom, lastUsedTriangle, TODO) ←  CommDiag lt none hom []
  logInfo m!"{newHom} et {homEnd}"
    if not (← isFinished newHom homEnd) then
      logInfo m! " reduce the right hand side"
      let (newHomEnd, _, newTODO) ← CommDiag lt none homEnd TODO

      FindPath2 lt newHom newHomEnd lastUsedTriangle newTODO


    else
      return TODO-/
