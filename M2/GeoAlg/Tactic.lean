import Mathlib

open Lean Meta Elab Tactic CategoryTheory

variable (C : Type) [Category C] [Inhabited C]
--variable (v : List Expr) (e : List <| Expr × (Fin v.length) × (Fin v.length))

-- pas de variable c'est plus simple surtout que après on va tout calculer
def v : List Expr := sorry
def e :  List <| List <| Expr × (Fin v.length) × (Fin v.length) := sorry


def J : Type := Fin v.length

def HomE (x y : J) : Fin e.length := sorry -- la liste des trucs de type x ⟶ y

-- peut etre virer le expr on verra
structure HomJ (x y : J) : Type where
  type : Fin e.length
  hom : Fin (e.get type).length
  dEq : ((e.get type).get hom).2.1 = x.val
  cdEq : ((e.get type).get hom).2.2 = y.val

instance QuiverJ : Quiver (J) := ⟨HomJ⟩

unsafe def diagObjE (x : J) : TacticM C:= do
  let h := v.get x
  let t ← inferType h
  guard <| ← isDefEq t (Expr.const `C [])
  evalExpr C (Expr.const `C []) h

unsafe def diagObj : TacticM <| J → C :=  do
  let mut l := []
  for i in [0: v.length] do
    let iFin : Fin v.length := ⟨i, by sorry⟩
    -- au pire pas grave si on ajoute une nouvelle source d'erreur
    l := l.cons (← diagObjE C iFin)

  return fun x => l[x.val]!

unsafe def diagMapE { a b : J } ( f : a ⟶ b) (x y : C) : TacticM (x ⟶ y):= do
  let t := e.get f.type
  let h := t.get f.hom
  let ty ← inferType h.1

  let homType ← mkAppM (``Quiver.Hom) #[v.get h.2.1, v.get h.2.2]
  guard <| ← isDefEq ty homType

  --let d ← diagObjE C v h.2.1
  --let cd ← diagObjE C v h.2.2
  -- la pour le coup on exploite à mort les possibilitées de unsafe
  evalExpr (x ⟶ y) homType h.1
/-
variable [Inhabited ((x : C) × (y : C) × (x ⟶ y))]

unsafe def diagMap (x y): TacticM <| Fin e.length → (Σ x : C, Σ y : C , x ⟶ y) :=  do
  let mut l := []
  for i in [0: e.length] do
    let iFin : Fin e.length := ⟨i, by sorry⟩
    let h := e.get iFin
    let t ← inferType h.1

    let homType ← mkAppM (``Quiver.Hom) #[v.get h.2.1, v.get h.2.2]
    guard <| ← isDefEq t homType

    let d ← diagObjE C h.2.1
    let cd ← diagObjE C h.2.2

    l := l.cons ⟨d, cd, ← evalExpr (d ⟶ cd) homType h.1⟩

  return fun x => l[x.val]!-/

unsafe def diag0 : TacticM <| Prefunctor J C := do
  let obj ← diagObj C
  --let map ← diagMap C v e

  let map {x y : J} : TacticM <| ( x ⟶ y) → (obj x ⟶ obj y) := do
    let truc: Inhabited (obj x ⟶ obj y) := sorry
    let mut l := []
    let n := HomE x y
    let xToY := e.get n

    for j in [1:3] do
      have : j< 4 := by
        --apply?
        sorry
      l := []

    for i in [0, xToY.length] do
      let iFin : Fin xToY.length := ⟨i, by sorry⟩
      let h := xToY.get iFin
      let t ← inferType h.1

      let homType ← mkAppM (``Quiver.Hom) #[v.get h.2.1, v.get h.2.2]
      guard <| ← isDefEq t homType

      --let d ← diagObjE C h.2.1
      --let cd ← diagObjE C h.2.2

      l := l.cons (← evalExpr (obj x ⟶ obj y) homType h.1)
    return (fun f => l.get ⟨f.hom.val,sorry⟩)


  let bidule ← map

  return ⟨obj , bidule⟩

    --sorry⟩

def diag  :  Prefunctor (Fin v.length) C where
  obj := sorry
  map := sorry



def isObjStep (l : List Expr) (e : Expr) : MetaM <| List Expr := do
  if ← isDefEq (← inferType e) (Expr.const `C []) then
    return e :: l
  else
    return l

def isHomStep (l : List <| Expr × Expr × Expr) (e : Expr) :  List <| Expr × Expr × Expr :=
  if e.isAppOf (``Quiver.Hom) then
    (e, e.getArg! 4,e.getArg! 5) :: l
  else
    l

variable (x : C)

def CST : Prefunctor J C where
  obj _ := x
  map _ := 𝟙 x

elab "BuildDiagram" : tactic => do
  let hyp ← getLocalHyps
  let listV := Array.foldlM isObjStep [] hyp
  let listH := Array.foldl isHomStep [] hyp

  --#check J

  let jDiag := "Jdiag".toName
  evalTactic <| ← `(tactic| set $(mkIdent jDiag) := Fin 4)
  evalTactic <| ← `(tactic| set $(mkIdent "Diag".toName) := CST C x)

  --let v := sorry
  --let e := sorry

  --let D := sorry

  --return

example {a b : C} (f : a ⟶ b) : True := by
  BuildDiagram
  sorry
