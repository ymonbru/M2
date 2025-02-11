--import Mathlib.Tactic
import Mathlib.Data.Nat.Defs
import Lean
import M2.CommDiagTactic.Dict

open Lean Meta Elab Tactic Std

variable (α : Type) [DecidableEq α]

/-- the data structure that remenber the info about a triangle relation in context-/
@[ext]
structure triangle where--f ≫ g = h
  f : α
  g : α
  h : α
  dir : Bool -- true if f ≫ g is on the letf side of the equation in the context
  proof : Expr
deriving Repr

/-- an extension of triangle that remember how it must be used in the context-/
@[ext]
structure rwTriangle extends triangle α where
  dep : Option Nat -- the position of the morphisme f in the sequence,  some if the rulle is used in the form f ≫ g ⟶  h, none if it's used on the form

/-- translate a rwTriangle into an executable tactic-/
def toTactic (t : rwTriangle α) : TacticM <| TSyntax `tactic := withMainContext do
  let proofTerm ← PrettyPrinter.delab t.proof
  match t.dep with
    | none => match t.dir with
      | false => `(tactic | conv => lhs; rw [($proofTerm)] )
      | true => `(tactic | conv => lhs; rw [← $proofTerm] )
    | some pos =>
      let posLit := Syntax.mkNumLit <| toString pos
      let posLitS := Syntax.mkNumLit <| toString (pos + 1)
      match t.dir with
      | false => `(tactic | slice_lhs $posLit $posLitS => rw [← $proofTerm] )
      | true => `(tactic | slice_lhs $posLit $posLitS => rw [ ($proofTerm) ] )

/- From here the function of the BFS exploration
The BFS algo will be performed by using a Dict remembering the explore states and the last step that lead to this state.

The date structure of Dict is very naive (with list) but the time  is manly due to excecution of tactic and not the data structure manipulation.-/

/-- the state of exploration is before ++ head ++ after = oldState, check if the triangle t can be expande from this position, and if it's the case add the path (if the new position is no new to the explored positions)

if a new state is found thenit's added to the queue in ordr to explore it later

if the state endState is found then an error containing the current explored states is raised
-/
def expand? (t : triangle α) (head : α) (before after oldState endState: List α) (explored : Dict (List α) (Option <| (List α) × rwTriangle α)) (storedStates : Queue (List α)) : Except (Dict (List α) (Option (List α × rwTriangle α))) (Queue (List α) × Dict (List α) (Option <| (List α) × rwTriangle α)) :=
  if t.h = head then
    let newState := before ++ t.f :: t.g :: after
    let (new?, newExplored) := Dict.add explored newState (some ⟨oldState, t, none⟩)
    if newState = endState then
      Except.error newExplored
    else
      if new? then
        Except.ok (storedStates.enqueue newState, newExplored)
      else
        Except.ok (storedStates, explored)
    else
      Except.ok (storedStates, explored)

/-- Same as expand? but the rule f ≫ g → h-/
def apply?  (t : triangle α) (head1 head2 : α) (pos : Nat) (before after oldState endState: List α) (explored : Dict (List α) (Option <| (List α) × rwTriangle α)) (storedStates : Queue (List α)): Except (Dict (List α) (Option (List α × rwTriangle α))) (Queue (List α) × Dict (List α) (Option <| (List α) × rwTriangle α)) :=
  if t.f = head1 ∧ t.g = head2 then
    let newState := before ++ t.h :: after
    let (new?, newExplored) := Dict.add explored newState (some ⟨oldState, t, some pos⟩)
    if newState = endState then
      Except.error newExplored
    else
      if new? then
        Except.ok (storedStates.enqueue newState, newExplored)
      else
        Except.ok (storedStates, explored)
  else
    Except.ok (storedStates, explored)

/-- compute inductively all the states that can be accessed from the curent state with only one triangle

pos is an invariant that remember the length of before in order to give rw triangle properly-/
def nextTriangle? (pos : Nat) (before curentState oldState endState: List α) (explored : Dict (List α) (Option <| List α × rwTriangle α) ) (t : triangle α) (storedStates : Queue (List α)) : Except (Dict (List α) (Option (List α × rwTriangle α))) (Queue (List α) × Dict (List α) (Option <| (List α) × rwTriangle α)) :=  match curentState with
  | [] => Except.ok (storedStates, explored)
  | [a] => do
    let (newStates, newExplored) ←  expand? α t a before [] oldState endState explored storedStates
    Except.ok (newStates, newExplored)
  | a :: b :: tail => do
    let (newStoredStates,newExplored) ←  nextTriangle? (pos + 1) (before ++ [a]) (b :: tail) oldState endState explored t storedStates
    let (newStoredStates, newExplored) ←  expand? α t a before (b :: tail) oldState endState newExplored newStoredStates
    apply? α t a b pos before tail oldState endState newExplored newStoredStates

/-- explore all the states that can be accessed from the current state by using any triangle on the list lt-/
def explore (state endState: List α) (explored : Dict (List α) (Option <| (List α) × rwTriangle α) ) (lt : List (triangle α)) (storedStates : Queue (List α)) : Except (Dict (List α) (Option (List α × rwTriangle α))) (Queue (List α) × Dict (List α) (Option <| (List α) × rwTriangle α)) := match lt with
  | [] => Except.ok (storedStates, explored)
  | t :: q => do
    let (newStoredStates, newExplored) ← nextTriangle? α 1 [] state state endState explored t storedStates
    explore state endState newExplored q newStoredStates

/-- algo BFS: if there is a state to explore in the queue, apply the function explore to it.

if an "error" is raised, then the final state is found so the path can be found by exploring explored otherwise try to perform an other step

it finishes because there is a finite number of states to explore and the can only be queued once-/
partial def BFS_step (stateStored : Queue (List α)) (lt : List (triangle α)) (endState : List α) (explored : Dict (List α) (Option <| List α × rwTriangle α)) : Dict (List α) (Option <| List α × rwTriangle α) :=
  match stateStored.dequeue? with
  | none => explored
  | some (state, stateStored) =>
    match explore α state endState explored lt stateStored with
      | Except.error newExplored => newExplored
      | Except.ok (newStoredStates, newExplored) => BFS_step newStoredStates lt endState newExplored

/-- apply BFS_step to get the Dict with the explored path until finding endState-/
def BFS (depState endState: List α ) (lt : List (triangle α)) : Dict (List α) (Option <| List α × rwTriangle α) :=

  let stateStored := Queue.empty.enqueue depState
  let explored := (Dict.empty.add depState none).2
  BFS_step α stateStored lt endState explored

/-- explore the Dict explored to find a path frome "state" to a reccord where there is no previous step to apply to get there. In other words the starting state-/
partial def findPathAux (explored : Dict (List α) (Option (List α × rwTriangle α))) (state : List α) (currentPath : List <| TSyntax `tactic): TacticM (List <| TSyntax `tactic) :=
    let previous := explored.find state
    match previous with
    | none => do throwError m!"No path found"
    | some none => return currentPath -- the only some none case is the dep state
    | some (some (prevState, t )) => withMainContext do
      let newCurrentPath := (← toTactic α t) :: currentPath
      findPathAux explored prevState newCurrentPath

/-- combine BFS and findPathAux to give bac the list of tactic to do in order to solve the goal.-/
def findPathBFS (lt : List (triangle α)) (dep fin : List α)  : TacticM (List <| TSyntax `tactic) := withMainContext do
  let explored := BFS α dep fin lt

  findPathAux α explored fin []
