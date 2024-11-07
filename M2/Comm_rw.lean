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
  proof : Expr
deriving Repr

/-- c represent the sequence of morphisms, the algo try to rewrite the rule coresponding to the triangle t

The boolean is true if nothing is changed and false otherwise-/
def applyTriangle (t : triangle) (c : List Expr ): TacticM (Bool × List Expr) := match c with
  |[] => return (true, c)
  |_ :: [] => return (true, c)
  |a :: b :: cprime => do
    if (← isDefEq a t.f) ∧ (← isDefEq b t.g) then

      let proofTerm ← Term.exprToSyntax t.proof
      evalTactic $ ← `(tactic| rw_assoc2 $proofTerm )

      logInfo m!"the composition {← ppExpr t.f} ≫ {← ppExpr t.g} is replaced by {← ppExpr t.h}"
      return (false, t.h :: cprime)
    else
      let (b,newc) ←  applyTriangle t (b::cprime)
      return (b, a::newc)

/-- The algo try every rewriting rule of the list lt to the sequence of morphisms.

The boolean is true if nothing is changed and false otherwise-/
def applyListTriangles (lt : List triangle) (c : List Expr ) : TacticM (Bool × List triangle × List Expr) :=
  match lt with
    |[] => return (true, [], c)
    |t::ltprime => do
      let (b, newc) ←  applyTriangle t c
      let (newbool, newlt, newc) ←  applyListTriangles ltprime newc
      if b then return (newbool, t::newlt, newc)
      else return (false, newlt, newc)


/-- The algo try to expand the rule t in the sequence c (expanding means that if t: f ≫ g = h and h is in c then h is replaced by f≫ g).

The boolean is true if nothing is changed and false otherwise-/
def expandTriangle (ok : Bool) (t : triangle) (c : List Expr ) : TacticM (Bool × List Expr ):=
  if not ok then return (false, c)
  else  match c with
    |[] => return (ok,c)
    |a :: cprime => do
      if  ← isDefEq t.h a then

      let proofTerm ← Term.exprToSyntax t.proof

      evalTactic $ ← `(tactic| first | rw [← $proofTerm] | rw [ ($proofTerm) ] )
      -- rw term in both direction to avoid problem when the triangle is on the other direction in the context.
      logInfo m!"the morphism {← ppExpr t.h} is replaced by the composition {← ppExpr t.f} ≫ {← ppExpr t.g}"
      return (false, t.f :: t.g :: cprime)
      else
        let (newok, newc) ←  expandTriangle  ok t cprime
        return (newok, a::newc)

/-- The algo try to expand the one rule of lt (and stops when it's done) in the sequence c .

The boolean is true if nothing is changed and false otherwise-/
def expandOneTriangle (lt : List triangle) (c : List Expr ) : TacticM (Bool × List triangle × List Expr) := match lt with
  |[]=> return (true, lt, c)
  |t :: ltprime => do
    let (b, newc) ←  expandTriangle true t c
    if b then
      let (newbool, ltprimeprime, newnewc) ←  expandOneTriangle ltprime c
      return (newbool, t::ltprimeprime, newnewc)
    else
      return (false, ltprime,newc)


/-- Apply all the reduction rules that can be applied, rewrite one backwards and continue while something has changed.
-/
 partial def CommDiag (lt:List triangle ) (lh : List Expr ) : TacticM (List Expr) := do
  let alt ←  applyListTriangles lt lh
  let eot ←  expandOneTriangle alt.2.1 alt.2.2

  if not eot.1 ∨ not alt.1 then
    CommDiag eot.2.1 eot.2.2
  else return alt.2.2
--The algo terminates because it continues while the length of lt is decreasing
