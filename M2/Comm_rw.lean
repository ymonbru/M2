import Mathlib.Tactic
import Mathlib.Data.Nat.Defs
import Lean
import M2.rw_assoc

open Lean Meta Elab Tactic

--variable (hom:Type) [DecidableEq hom] [ToString hom]--(andThen: hom → hom → hom) --[Std.Associative  andThen]

--(andThenAssoc: ∀ f g h, andThen f (andThen g h)= andThen (andThen f g) h)

--variable {obj:Type} (dom codom: hom → obj)

@[ext]
structure triangle where--f ≫ g = h
  f : Expr
  g : Expr
  h : Expr
  proof : Expr
  --trg_com: andThen f g = h
deriving Repr

-- le booléen est à true si on n'a rien changé et false si on à modifié un truc
def applyTriangle (t : triangle) (c : List Expr ): TacticM (Bool × List Expr) := match c with
  |[] => return (true, c)
  |_ :: [] => return (true, c)
  |a :: b :: cprime => do
    if (← isDefEq a t.f) ∧  (← isDefEq b t.g) then

      let proofTerm ← Term.exprToSyntax t.proof
      evalTactic $ ← `(tactic| rw_assoc $proofTerm )

      logInfo m!"the composition {← ppExpr t.f} ≫ {← ppExpr t.g} is replaced by {← ppExpr t.h}"
      return (false, t.h :: cprime)
    else
      let (b,newc) ←  applyTriangle t (b::cprime)
      return (b, a::newc)

-- le booléen est à true si on n'a rien changé et false si on à modifié un truc
def applyListTriangles (lt : List triangle) (c : List Expr ) : TacticM (Bool × List triangle × List Expr) :=
  match lt with
    |[] => return (true, [], c)
    |t::ltprime => do
      let (b, newc) ←  applyTriangle t c
      let (newbool, newlt, newc) ←  applyListTriangles ltprime newc
      if b then return (true, t::newlt, newc)
      else return (newbool, newlt, newc)


-- le booléen est à true si on n'a rien changé et false si on à modifié un truc
def expandTriangle (ok : Bool) (t : triangle) (c : List Expr ) : TacticM (Bool × List Expr ):=
  if not ok then return (false, c)
  else  match c with
    |[] => return (ok,c)
    |a :: cprime => do
      if  ← isDefEq t.h a then

      let proofTerm ← Term.exprToSyntax t.proof
      evalTactic $ ← `(tactic| rw [← $proofTerm] )

      logInfo m!"the morphism {← ppExpr t.h} is replaced by the composition {← ppExpr t.f} ≫ {← ppExpr t.g}"
      return (false, t.f :: t.g :: cprime)
      else
        let (newok, newc) ←  expandTriangle  ok t cprime
        return (newok, a::newc)

-- le booléen est à true si on n'a rien changé et false si on à modifié un truc
def expandOneTriangle (lt : List triangle) (c : List Expr ) : TacticM (Bool × List triangle × List Expr) := match lt with
  |[]=> return (true, lt, c)
  |t :: ltprime => do
    let (b, newc) ←  expandTriangle true t c
    if b then
      let (newbool, ltprimeprime, newnewc) ←  expandOneTriangle ltprime c
      return (newbool, t::ltprimeprime, newnewc)
    else
      return (false, ltprime,newc)

 partial def CommDiag (lt:List triangle ) (lh : List Expr ) : TacticM (List Expr) := do
  let alt ←  applyListTriangles lt lh
  let eot ←  expandOneTriangle alt.2.1 alt.2.2

  if not eot.1 then
    CommDiag eot.2.1 eot.2.2
  else return alt.2.2
/-termination_by lt
decreasing_by
  calc sizeOf eot.2.1 < sizeOf alt.2.1  := by {
        apply expandOneTriangleDec
        apply Bool.not_inj_iff.mp
        rw [hyp]
        simp}
        _ ≤ sizeOf lt  := by apply applyListTrianglesDec-/
