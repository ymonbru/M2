import Mathlib
import Qq

open Qq Lean Meta Elab Tactic CategoryTheory

universe u v

variable {Cate: Type u} [Quiver.{v+1,u} Cate] -- ici il faut un +1


def isObjStep (cat : Expr) (e : Expr) (l : List Expr) : TacticM <| List Expr := do
  if ← isDefEq (← inferType e) cat  then
    return e :: l
  else
    return l

def isHomStep (cat : Expr) (l : List <| Expr × Expr × Expr) (e : Expr) : TacticM <|  List <| Expr × Expr × Expr := do
  let typeE ← inferType e
  let x ←  mkFreshExprMVar cat
  let y ←  mkFreshExprMVar cat
  let h ← mkAppOptM ``Quiver.Hom #[cat, none, x, y]
  if ← isDefEq typeE h then
    return ⟨e,x,y⟩ :: l
  else
    return l

def mkFinE {n : Nat} (x : Fin n) : TacticM Expr := do
  let nQ : Q(Nat) := Expr.lit (Literal.natVal n)
  let xQ : Q(Nat) := Expr.lit (Literal.natVal x.val)

  -- vraiment pas ouf du tout mais on verra mieux plus tard
  let ineq  ← mkAppM ``LT.lt #[xQ,nQ]
  let newGoal ← mkFreshExprMVar ineq
  appendGoals [newGoal.mvarId!]
  evalTactic <| ← `(tactic| rotate_left; repeat decide)
  mkAppM ``Fin.mk #[xQ, newGoal]


variable {v : List Cate} (l : List <| Σ a b : Fin v.length, v.get a ⟶ v.get b)

def mkHomNum (cat : Q(Type)) (vE : List Q($cat)) (f : Expr × Expr × Expr): TacticM <| Expr × Expr × Expr := do
  let l := List.ofFn (fun x => x : Fin vE.length → Fin vE.length)
  let ox ← List.findM? (fun x => isDefEq (vE.get x) f.2.1) l
  let oy ← List.findM? (fun x => isDefEq (vE.get x) f.2.2) l
  match ox, oy with
    |none, _ => throwError "A morphism is not in the context, this should not append"
    |_, none => throwError "A morphism is not in the context, this should not append"
    |some x, some y => do
      let xQ ← mkFinE x
      let yQ ← mkFinE y

      return ⟨f.1,xQ,yQ⟩




--est-ce que ce ne serait pas usine à gaz ça?
-- surement à corriger quand on aura un truc qui marche
def baseE (f :  Σ a b : Fin v.length, v.get a ⟶ v.get b) (e : Π a b : Fin v.length, List (v.get a ⟶ v.get b)): Π a b : Fin v.length, List (v.get a ⟶ v.get b) := fun a b => sorry/-
  if h: a = f.1 ∧ b = f.2.1 then

    f.2.2 :: e a b
  else
    e a b-/

def e : Π a b : Fin v.length, List (v.get a ⟶ v.get b) :=
  List.foldr baseE (fun _ _ => []) l

def toNb : List <| List Nat := List.ofFn (fun x => List.ofFn (fun k => (e l x k).length))

def QuivJ (x y : Fin v.length): Type :=
  let h := toNb l
  let a : Fin h.length := ⟨x.val, Fin.val_lt_of_le x (le_of_eq (by simp [h,toNb]))⟩
  let b : Fin (h.get a).length := ⟨y.val, Fin.val_lt_of_le y (le_of_eq (by simp [h, a, toNb]))⟩

  Fin <| ((h.get a).get b)

def ObjMapJ : Fin v.length → Cate := v.get

def FunMapJ  {x y : Fin v.length} (f : QuivJ l x y) : (ObjMapJ x ⟶ ObjMapJ y) := (e l x y).get ⟨f.val, Fin.val_lt_of_le f (le_of_eq (by simp [toNb]))⟩

def mkSigma (x y : Fin v.length) (f : v.get x ⟶ v.get y) : Σ a b : Fin v.length, v.get a ⟶ v.get b := Sigma.mk x (Sigma.mk y f)

def mkSigmaE (v : Expr) (f : Expr × Expr × Expr) : TacticM Expr := do
  mkAppOptM ``mkSigma #[none, none, v, f.2.1, f.2.2, f.1]

def consE (l : List Expr) (t : Expr) : TacticM Expr := do
  let nil ← mkAppOptM ``List.nil #[t]
  List.foldrM (fun e l => mkAppM ``List.cons #[e, l]) nil l

def mkTypeAux (l : List Cate) : Type v := (Σ a b : Fin l.length, List.get l a ⟶ List.get l b)


elab "BuildDiagram_of" cat:term : tactic => do
  let cat : Q(Type) ← Term.elabTerm cat none
  let uQ ← mkFreshLevelMVar
  let vQ ← mkFreshLevelMVar
  --pas beau du tout mais on verra après
  let QuivCat := Expr.app (Expr.const `Quiver [vQ, uQ]) cat
  let newGoal ← mkFreshExprMVar QuivCat
  appendGoals [newGoal.mvarId!]

  evalTactic <| ← `(tactic| rotate_left; assumption)--changer le assumption

  let hyp ← getLocalHyps

  let listV ←  Array.foldrM (isObjStep cat) [] hyp
  let listVE : Q(List $cat) ← consE listV cat

  let listH ←  Array.foldlM (isHomStep cat) [] hyp
  logInfo m!"{listH}"
  let listH ← listH.mapM (mkHomNum cat listV)
  let listH ← listH.mapM (mkSigmaE listVE)

  let t ← mkAppM ``mkTypeAux #[listVE]
  let listHE ← consE listH.reverse t

  logInfo m!"{← ppExpr listVE}"
  logInfo m!"{← ppExpr listHE}"

  let n := listV.length
  let nQ : Q(Nat) := Expr.lit (Literal.natVal n)
  let J : Q(Type) := mkApp q(Fin) nQ

  let QuivJ ← mkAppOptM ``QuivJ #[none, none, listVE, listHE]
  let instQuiverJ ← mkAppOptM ``Quiver.mk #[J, QuivJ]

  let FunObjJ ← mkAppOptM ``ObjMapJ #[none, listVE]
  let FunMapJ ← mkAppOptM ``FunMapJ #[none, none, listVE, listHE]


  let DiagJ  ← mkAppOptM ``Prefunctor.mk #[J,instQuiverJ, cat, newGoal , FunObjJ, FunMapJ ]

  --let Diag ← mkAppOptM ``Paths.lift #[J, instQuiverJ, none, none, DiagJ]

  --netoyer le bazard de mkFinE assumption c'est pour QuivCat
  --evalTactic <| ← `(tactic| rotate_left; repeat decide;assumption)

  evalTactic <| ← `(tactic| set $(mkIdent `J) : Type := $(← Term.exprToSyntax J))
  evalTactic <| ← `(tactic| set $(mkIdent "QuivJ".toName) := $(← Term.exprToSyntax instQuiverJ))
  evalTactic <| ← `(tactic| set $(mkIdent "Diag".toName) := $(← Term.exprToSyntax DiagJ))

variable (C2: Type u) [Quiver.{v+1,u} C2]
example {x y : C2} (k : x ⟶ y) {a b c d : Cate} (f: a ⟶ b) (g : c ⟶ b) : 1=2 := by

  BuildDiagram_of Cate

  BuildDiagram_of AlgebraicGeometry.Scheme



  have : Diag.obj 1 = b := by rfl
  have : Diag.map (⟨0, by simp [toNb, mkSigma, e, baseE ];sorry ⟩ : QuivJ.Hom 0 1 ) = f := by rfl


  sorry


/-
unsafe def diagObjE (x : J) : TacticM C:= do
  let h := v.get x
  let t ← inferType h
  guard <| ← isDefEq t (Expr.const `C [])
  evalExpr C (Expr.const `C []) h

unsafe def diagObj : TacticM <| J → C :=  do
  let mut l := []
  for h : i in [0: v.length] do
    let iFin : Fin v.length := ⟨i, Membership.mem.upper h⟩
    -- au pire pas grave si on ajoute une nouvelle source d'erreur
    l := l.cons (← diagObjE C iFin)

  return fun x => l[x.val]!-/

/-unsafe def diagMapE { a b : J } ( f : a ⟶ b) (x y : C) : TacticM (x ⟶ y):= do
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

unsafe def diag0 : TacticM <| (Prefunctor J C) := do
  let obj ← diagObj C
  --let map ← diagMap C v e

  let map {x y : J} : TacticM <| ( x ⟶ y) → (obj x ⟶ obj y) := do
    let mut l := []
    let n := HomE x y
    let xToY := e.get n

    for h : i in [0: xToY.length] do
      let iFin : Fin xToY.length := ⟨i, Membership.mem.upper h⟩
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
  map := sorry-/



elab "#expr" "[" t:term "]" : command =>
  Command.liftTermElabM do
  let t ← Term.elabTerm t none
  let t ← instantiateMVars t
  logInfo m!"Expression: {t}:\n{repr t}"
  --let t ← reduce t
  --let t ← instantiateMVars t
  --logInfo m!"Reduced: {t}:\n{repr t}"

#check Prefunctor
variable (a b c : Cate) (f : a ⟶ b) (g : c ⟶ b)

def v1: List Cate := [a, b, c]

#check v1
def e2 (x y : Fin 3) : List ([a,b,c].get x ⟶ [a,b,c].get y) := match x,y with
    |0,1 => [f]
    |2,1 => [g]
    | _,_ => []

#eval q( fun (x y : Fin 3) (a : Cate) (f : a ⟶ a) => match x,y with
    |0,1 => [f]
    | _,_ => [])

#eval q(fun x : Fin 1 => [1].get x )

#expr [e2]

variable (x : C)

#expr [x]
#expr [Prefunctor (Fin 4) (Fin 4)]



def CST : Prefunctor J C where
  obj _ := x
  map _ := 𝟙 x

#expr [CST]
