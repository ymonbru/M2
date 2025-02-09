--import Mathlib.Tactic
import Mathlib.Data.Nat.Defs
import Lean
--import M2.CommDiagTactic.rw_assoc
import M2.CommDiagTactic.Dict

open Lean Meta Elab Tactic

@[ext]
structure triangle where--f ≫ g = h
  f : Nat
  g : Nat
  h : Nat
  dir : Bool -- true if f ≫ g is on the letf side of the equation in the context
  proof : Expr
deriving Repr

@[ext]
structure rwTriangle extends triangle where
  red : Bool-- true if the rulle is used in the form f ≫ g ⟶  h, false if it's used on the form


def nextTriangle? (state: List Nat) (explored : Dict (List Nat) (rwTriangle) ) (t : triangle) : MetaM <| List (List Nat) × Dict (List Nat) (rwTriangle) := do match state with
  | [] => return ([], explored)
  | a :: q => if a = t.h then
                let newState := [t.f, t.g]
                let (new?, newExplored) := Dict.add explored newState (⟨t, false⟩)
                if new? then
                  return ([newState], newExplored)
                else
                  return ([], explored)

              else
                return ([], explored)
  | a :: b :: tail => sorry
