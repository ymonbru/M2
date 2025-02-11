import Lean

open Lean Meta Elab Tactic


variable {α : Type} {β : Type } [DecidableEq α]

/-- a naive data structure of dictionary, the time of these operations is not the limiting factor in their use-/
structure Dict (α β : Type) where
  data : List (α × β)

namespace Dict

/-- the empty dictionary-/
def empty : Dict α β :=
  ⟨[]⟩

/-- if there is no entry at key then add it to the list and tell with the Bool if it was added-/
def addAux (d : List <| α × β) (key : α) (value : β) : Bool × (List <| α × β ):= match d with
  | [] => (true, [(key, value)])
  | (k, v) :: tail => if k = key then (false, d)
                      else
                        let (b, newD) :=  addAux tail key value
                        (b, (k, v) :: newD)

/-- same as addAux but with dictionary and not lists-/
def add (d : Dict α β) (key : α ) (value : β) : Bool × Dict α β :=
  let (b, newD) :=  addAux d.data key value
  (b, ⟨newD⟩)

/-- find a reccord with key "key" and give it-/
def findAux (d : List <| α × β) (key : α) : Option β := match d with
  | [] => none
  | (k, v) :: tail => if k = key then some v else findAux tail key

/-- same as findAux but with dictionary and not lists-/
def find (d : Dict α β) (key : α) : Option β :=
  findAux d.data key

end Dict
