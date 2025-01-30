import Lean

open Lean Meta Elab Tactic

/- une structure naive de dictionaire, on fera mieux plus tard-/
variable {α : Type} {β : Type } [DecidableEq α]

structure Dict (α β : Type) where
  data : List (α × β)

namespace Dict




def empty : Dict α β :=
  ⟨[]⟩

def addAux (d : List <| α × β) (key : α) (value : β) : Bool × (List <| α × β ):= match d with
  | [] => (true, [(key, value)])
  | (k, v) :: tail => if k = key then (false, d)
                      else
                        let (b, newD) :=  addAux tail key value
                        (b, (k, v) :: newD)

def add (d : Dict α β) (key : α ) (value : β) : Bool × Dict α β :=
  let (b, newD) :=  addAux d.data key value
  (b, ⟨newD⟩)

def findAux (d : List <| α × β) (key : α) : Option β := match d with
  | [] => none
  | (k, v) :: tail => if k = key then some v else findAux tail key

def find (d : Dict α β) (key : α) : Option β :=
  findAux d.data key


end Dict
