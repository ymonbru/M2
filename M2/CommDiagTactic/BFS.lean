import Mathlib.Tactic
import Mathlib.Data.Nat.Defs
import Lean
import M2.CommDiagTactic.rw_assoc
import M2.CommDiagTactic.Dict

open Lean Meta Elab Tactic Std

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

def toTactic (t : rwTriangle) : TacticM <| TSyntax `tactic := do
  let proofTerm ← PrettyPrinter.delab t.proof
  match t.dir, t.red with
    -- ou peut être l'autre sens
    | false, false => `(tactic| conv => lhs; rw [($proofTerm)] )
    | true, false => `(tactic| conv => lhs; rw [← ($proofTerm)] )
    | _, true =>
      let tac ← rw_assoc_lhs_suggest proofTerm
      match tac with
        | none => `(tactic| skip)
        | some tac => return tac


    --`(tactic| rw_assoc_lhs $proofTerm )
    --TODO: implementer une version de rw_assoc ou on passe la direction en argument


def expand? (t : triangle) (head : Nat) (before after oldState : List Nat) (explored : Dict (List Nat) (Option <| (List Nat) × rwTriangle)) (storedStates : Queue (List Nat)): Queue (List Nat) × Dict (List Nat) (Option <| List Nat × rwTriangle) :=
  if t.h = head then
    let newState := before ++ t.f :: t.g :: after
    let (new?, newExplored) := Dict.add explored newState (some ⟨oldState, t, false⟩)
    if new? then
      (storedStates.enqueue newState, newExplored)
    else
      (storedStates, explored)
  else
    (storedStates, explored)

def apply?  (t : triangle) (head1 head2 : Nat) (before after oldState: List Nat) (explored : Dict (List Nat) (Option <| (List Nat) × rwTriangle)) (storedStates : Queue (List Nat)): Queue (List Nat) × Dict (List Nat) (Option <| (List Nat) × rwTriangle) :=
  if t.f = head1 ∧ t.g = head2 then
    let newState := before ++ t.h :: after
    let (new?, newExplored) := Dict.add explored newState (some ⟨oldState, t, true⟩)
    if new? then
      (storedStates.enqueue newState, newExplored)
    else
      (storedStates, explored)
  else
    (storedStates, explored)


def nextTriangle? (before curentState oldState : List Nat) (explored : Dict (List Nat) (Option <| List Nat × rwTriangle) ) (t : triangle) (storedStates : Queue (List (Nat))) : Queue (List Nat) × Dict (List Nat) (Option <| List Nat × rwTriangle) :=  match curentState with
  | [] => (storedStates, explored)
  | [a] => let (newStates, newExplored) := expand? t a before [] oldState explored storedStates
           (newStates, newExplored)
  | a :: b :: tail =>
    let (newStoredStates,newExplored) := nextTriangle? (before ++ [a]) (b :: tail) oldState explored t storedStates
    let (newStoredStates, newExplored) := expand? t a before (b :: tail) oldState newExplored newStoredStates
    apply? t a b before tail oldState newExplored newStoredStates

def explore (state : List Nat) (explored : Dict (List Nat) (Option <| (List Nat) × rwTriangle) ) (lt : List triangle) (storedStates : Queue (List Nat)): Queue (List Nat) × Dict (List Nat) (Option <| (List Nat) × rwTriangle) := match lt with
  | [] => (storedStates, explored)
  | t :: q =>
    let (newStoredStates, newExplored) := nextTriangle? [] state state explored t storedStates
    explore state newExplored q newStoredStates

partial def BFS_step (stateStored : Queue (List Nat)) (lt : List triangle) (explored : Dict (List Nat) (Option <| (List Nat) × rwTriangle)): Dict (List Nat) (Option <| (List Nat) × rwTriangle) :=
  match stateStored.dequeue? with
  | none => explored
  | some (state, stateStored) =>
    let (newStoredStates, newExplored) := explore state explored lt stateStored
    BFS_step newStoredStates lt newExplored

def BFS (dep : List Nat ) (lt : List triangle) : Dict (List Nat) (Option <| (List Nat) × rwTriangle) :=

  let stateStored := Queue.empty.enqueue dep
  let explored := (Dict.empty.add dep (none : Option <| (List Nat) × rwTriangle)).2
  BFS_step stateStored lt explored

def aff (d : List ℕ × Option (List ℕ × rwTriangle)): List ℕ × Option (List ℕ ):=
  match d with
  | (a, none) => (a, none)
  | (a, some (b, _)) => (a, some b)

partial def findPathAux (explored : Dict (List Nat) (Option (List Nat × rwTriangle))) (state : List Nat) (currentPath : List <| TSyntax `tactic): TacticM (List <| TSyntax `tactic) :=
    let previous := explored.find state
    match previous with
    | none => do throwError m!"No path found"
    | some none => return currentPath -- the only some none case is the dep state
    | some (some (prevState, t )) => do
      let newCurrentPath := (← toTactic t) :: currentPath
      findPathAux explored prevState newCurrentPath

def findPathBFS (lt : List triangle) (dep fin : List Nat)  : TacticM (List <| TSyntax `tactic) := do
  let explored := BFS  dep lt

  --logInfo m!"explored: {explored.affKeys.map aff}"

  findPathAux explored fin []
