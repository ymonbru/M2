import Mathlib

variable (l : List <| Nat × Nat) (nb : Nat)

def succ (l : List <| Nat × Nat) (x : Nat) : List Nat := match l with
  | [] => []
  | t :: q => if t.1 = x then t.2 :: (succ q x)
              else (succ q x)

def pred (l : List <| Nat × Nat) (x : Nat) : List Nat := match l with
  | [] => []
  | t :: q => if t.2 = x then t.1 :: (pred q x)
              else (pred q x)

variable (s : Nat → List Nat) (p : Nat → List Nat)

def diag (x : Nat) : Option <| Nat × Nat × Nat := do
  let f : Nat → (Option <| Nat × Nat × Nat) := fun y => do
    let z ← (s x).find? (fun t => t ≠ y ∧ not ((s y).inter (s t)).isEmpty)
    let d ← ((s y).inter (s z)).head?
    return ⟨y,z,d⟩
  let w ← (s x).find? (fun t => (f t).isSome)
  f w
  -- niveau complexité c'est pas fou, mais comme sur mes exemples s sera de taille au plus deux, ça ne devrait pas poser de problemes

#eval let l := [(1,2),(1,3),(2,4),(3,4)]
      let s := fun x => succ l x
      let p := fun x => pred l x
      diag p 4

-- mesure si compte tenu des points déjà placés (i,j)--a peut etre vertical (true) horizontal (false) ou les deux (error true) ou rien du tout: (error false)
def isCompatVertic (grid : List <| Option <| ℕ × ℕ ) (a i j : Nat) : Option (Option Bool) := do
  let ca ← grid[a]?
  match ca with
    |none => return none
    |some (xa,ya) =>
      if xa = i ∧ ya = j+1 then
        return true
      else
        if xa = i+1 ∧ ya = j then
          return false
        else
          --normelement ça n'arrivera pas
          none

def isCompatSquare (grid : List <| Option <| ℕ × ℕ ) (a b i j : Nat) : Option (Option Bool) := do
  let ova ← isCompatVertic grid a i j
  let ovb ← isCompatVertic grid b i j
  return do
    let va ← ova
    let vb ← ovb
    return va ∧ not vb

partial def addCord (grid : List <| Option <| ℕ × ℕ ) (x i j: Nat) :  List <| Option <| ℕ × ℕ :=
  let cx := (grid.getD x none)
  match cx with
    | some (u,v) =>
      if u = i ∧ v = j then grid
      else failure
    | none =>
      let grid := grid.modify x (fun _ => some (i,j))
      let u := diag p x
      let d := diag s x
      match d,u with
        |none, none => grid
        |some (a,b,c), none =>
          let cs := isCompatSquare grid a b i j
          match cs with
            |none => failure
            |some false =>
              let grid := addCord grid b i (j+1)
              grid
            | _ =>
              let grid := addCord grid a i (j+1)
              grid
        |none, some (y,z,w) => sorry
        |some (a,b,c), some (y,z,w) => sorry
