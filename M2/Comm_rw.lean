import Mathlib.Tactic
import Mathlib.Data.Nat.Defs
import Lean
import M2.rw_assoc

open Lean Meta Elab Tactic
@[ext]
structure triangle where--f ≫ g = h
  f : Expr
  g : Expr
  h : Expr
  --used : Bool
  proof : Expr
deriving Repr


/-- hom represent the sequence of morphisms, the algo try to rewrite the rule coresponding to the triangle t

The boolean is true if nothing is changed and false otherwise-/
def applyTriangle (t : triangle) (hom : List Expr ) : TacticM (Bool × List Expr) := withMainContext do
match hom with
  | [] => return (true, hom)
  | _ :: [] => return (true, hom)
  | a :: b :: homPrime =>
    if (← isDefEq a t.f) ∧ (← isDefEq b t.g) then

      --let proofTerm ← Term.exprToSyntax t.proof
      --evalTactic $ ← `(tactic| first | rw_assoc2 $proofTerm | skip  )

      logInfo m!"the composition {← ppExpr t.f} ≫ {← ppExpr t.g} is replaced by {← ppExpr t.h}"

      return (false, t.h :: homPrime)
    else
      let (unchanged?, newHom) ←  applyTriangle t (b::homPrime)
      return (unchanged?, a::newHom)

/-- The algo try every rewriting rule of the list lt to the sequence of morphisms.

The boolean is true if nothing is changed and false otherwise-/
def applyListTriangles (lt : List triangle) ( lastUsed : Option triangle) (hom : List Expr ) (tacticTODO: List <| TSyntax `tactic): TacticM (Bool × List triangle × Option triangle × List Expr × (List <| TSyntax `tactic)) :=
  match lt with
    | [] => return (true, [], lastUsed, hom, tacticTODO)
    | t :: ltQ => do
      let (newbool, newlt, newLastUsed, newHom, newTacticTODO) ←  applyListTriangles ltQ lastUsed hom tacticTODO
      let (b, nnewHom) ←  applyTriangle t newHom

      if b then
        return (newbool, t :: newlt, newLastUsed, newHom, newTacticTODO)
      else
        let proofTerm ← Term.exprToSyntax t.proof
        let tac ← `(tactic| first | rw_assoc2 $proofTerm | skip  )
        return (false, newlt, some t , nnewHom, tac :: newTacticTODO)


/-- The algo try to expand the rule t in the sequence c (expanding means that if t: f ≫ g = h and h is in c then h is replaced by f≫ g).

The boolean is true if nothing is changed and false otherwise-/
def expandTriangle (ok : Bool) (t : triangle) (hom : List Expr ) : TacticM (Bool × List Expr ):= withMainContext do
  if not ok then return (false, hom)
  else  match hom with
    |[] => return (ok, hom)
    |a :: homQ =>
      if  ← isDefEq t.h a then

      --let proofTerm ← Term.exprToSyntax t.proof
      --evalTactic $ ← `(tactic| first | rw [← $proofTerm] | rw [ ($proofTerm) ]| skip )

      -- rw term in both direction to avoid problem when the triangle is on the other direction in the context.
      logInfo m!"the morphism {← ppExpr t.h} is replaced by the composition {← ppExpr t.f} ≫ {← ppExpr t.g}"

      return (false, t.f :: t.g :: homQ)
      else
        let (newok, newHom) ←  expandTriangle  ok t homQ
        return (newok, a :: newHom)

/-- The algo try to expand the one rule of lt (and stops when it's done) in the sequence hom .

The boolean is true if nothing is changed and false otherwise-/
def expandOneTriangle (lt : List triangle) (lastUsed : Option triangle) (hom : List Expr ) (tacticTODO: List <| TSyntax `tactic): TacticM (Bool × Option triangle × List triangle × List Expr × (List <| TSyntax `tactic) ) := match lt with
  | []=> return (true, lastUsed, lt, hom, tacticTODO)
  | t :: ltQ => do
    let (b, newHom) ←  expandTriangle true t hom
    if b then
      let (expanded?, newLastUsed, newLt, nnewHom, newTacticTODO) ←  expandOneTriangle ltQ lastUsed newHom tacticTODO
      return (expanded?, newLastUsed, t::newLt, nnewHom, newTacticTODO)
    else
      let proofTerm ← Term.exprToSyntax t.proof
      let tac ← `(tactic| first | repeat rw [← $proofTerm] | rw [ ($proofTerm) ]| skip )

      return (false, some t, ltQ, newHom, tac :: tacticTODO)


/-- Apply all the reduction rules that can be applied, rewrite one backwards and continue while something has changed.-/
partial def CommDiag (lt : List triangle) (lastUsed : Option triangle) (Hom : List Expr ) (tacticTODO: List <| TSyntax `tactic): TacticM <| List Expr × Option triangle × (List <| TSyntax `tactic) := do

  let (modif?aplt, newLt, newLastUsed, newHom, newTacticTODO) ←  applyListTriangles lt lastUsed Hom tacticTODO
  let (modif?eot, nnewLastUsed, nnewLt, nnewHom, nnewTacticTODO) ←  expandOneTriangle newLt newLastUsed newHom newTacticTODO

  if not modif?eot ∨ not modif?aplt then
    CommDiag nnewLt nnewLastUsed nnewHom nnewTacticTODO
  else
    return (nnewHom, nnewLastUsed, nnewTacticTODO.reverse)
    --reverse is for being in the right order
    /-if not (← isFinished nnewHom HomEnd) then
    -- si ce n'est pas au bout, il faut défaire des trucs déja faits
      match nnewLtUsed with
        | [] => return nnewHom
        | t :: ltUsedPrime =>

        --undo t: vraiment aussi dans la liste des homs
          let proofTerm ← Term.exprToSyntax t.proof
          evalTactic $ ← `(tactic| first | rw [← $proofTerm] | rw [ ($proofTerm) ] | rw_assoc2 $proofTerm | skip )

          CommDiag  (t::nnewLt).reverse ltUsedPrime nnewHom HomEnd
    else
      return nnewHom-/
--The algo terminates because it continues while the length of lt is decreasing



def clear (usedT : triangle) (lt : List triangle) : MetaM <| List triangle :=
  match lt with
    | [] => return []
    | t :: q => do
      if ← isDefEq t.proof usedT.proof then
        clear usedT q-- in case the relation is present many times
      else
        return t :: (← clear usedT q)

def isFinished (hom homEnd : List Expr) : MetaM Bool :=
  match hom, homEnd with
  | [], [] => return true
  | h1 :: homQ, h2 :: homEndQ => do
    if (← isDefEq h1 h2) then
      isFinished homQ homEndQ
    else
      return false
  | _, _ => return false

partial def FindPath2 (lt : List triangle) (hom homEnd : List Expr): TacticM <| List <| TSyntax `tactic := withMainContext do-- beacause the context has changed
  let (newHom, lastUsedTriangle, TODO) ←  CommDiag lt none hom []
    if not (← isFinished newHom homEnd) then
      --let (newHomEnd, newLastUsedTriangle, newTODO) ← CommDiag lt lastUsedTriangle homEnd TODO
      --if not (← isFinished newHom newHomEnd) then

        logInfo m!"START AGAIN"
        match lastUsedTriangle with
          | none => pure []
          | some t  =>
              let newLt ←  clear t lt
              FindPath2 newLt hom homEnd
      --else
        --return newTODO
    else
      return TODO
