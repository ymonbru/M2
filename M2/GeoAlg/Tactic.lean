import Mathlib
import Qq

open Qq Lean Meta Elab Tactic CategoryTheory



def Cate : Type := sorry
instance : Quiver  Cate := by
  refine { Hom := ?_ }
  exact fun x y => Nat

def isObjStep (e : Expr) (l : List Expr) : TacticM <| List Expr := do
  if ← isDefEq (← inferType e) (Expr.const ``Cate [])  then
    return e :: l
  else
    return l

def isHomStep (l : List <| Expr × Expr × Expr) (e : Expr) : TacticM <|  List <| Expr × Expr × Expr := do
  --logInfo m!"{← ppExpr e}"
  let typeE ← inferType e
  if typeE.isAppOf (``Quiver.Hom) then

    return (e, typeE.getArg! 2,typeE.getArg! 3) :: l
  else
    return l


variable (v : List Cate) (e : Π a b : Fin v.length, List (v.get a ⟶ v.get b))

def toNb : List <| List Nat := List.ofFn (fun x => List.ofFn (fun k => (e x k).length))

def QuivJ (x y : Fin v.length): Type :=
  let h := toNb v e
  let a : Fin h.length := ⟨x.val, Fin.val_lt_of_le x (le_of_eq (by simp [h,toNb]))⟩
  let b : Fin (h.get a).length := ⟨y.val, Fin.val_lt_of_le y (le_of_eq (by simp [h, a, toNb]))⟩

  Fin <| ((h.get a).get b)

def ObjMapJ : Fin v.length → Cate := v.get

def FunMapJ  {x y : Fin v.length} (f : QuivJ v e x y) : (ObjMapJ v x ⟶ ObjMapJ v y) := (e x y).get ⟨f.val, Fin.val_lt_of_le f (le_of_eq (by simp [toNb]))⟩



def isCompatible (x y : Expr) (e: Expr × Expr × Expr) : TacticM Bool := do
  return (← isDefEq x e.2.1) && (← isDefEq y e.2.2)

#check Quiver.mk
#check List.foldlM
#check List.get

elab "BuildDiagram" : tactic => do
  let hyp ← getLocalHyps
  let listV ←  Array.foldrM isObjStep [] hyp
  let listH ←  Array.foldlM isHomStep [] hyp
  let listVE ← List.foldrM (fun e l => mkAppM ``List.cons #[e, l]) (q(List.nil) : Q(List Cate)) listV


  --terriblement pas obptimal tout ce bazard
  let mut listHE := []
  let mut listN := []
  for x in listV.reverse do
    let mut listHEx := []
    let mut listNx := []
    for y in listV.reverse do


      let Hxy ← listH.filterM (isCompatible x y)
      let nxy : Q(Nat) := Expr.lit (Literal.natVal Hxy.length)
      listNx := nxy :: listNx


      let nilExy ← mkAppOptM ``List.nil #[← mkAppM ``Quiver.Hom #[x, y]]
      let Hxy ← List.foldrM (fun e l => mkAppM ``List.cons #[e.1, l]) nilExy Hxy
      listHEx := Hxy :: listHEx

    let nilEn ← mkAppOptM ``List.nil #[q(Nat)]
    let Nx ← List.foldrM (fun e l => mkAppM ``List.cons #[e, l]) nilEn listNx

    listN := Nx :: listN
    listHE := listHEx :: listHE

  let truc := q(fun (x y : Nat) => ((listHE.get! x).get! y))

  let nilEln ← mkAppOptM ``List.nil #[q(List Nat)]

  let QuivJE ← List.foldrM (fun e l => mkAppM ``List.cons #[e, l]) nilEln listN

  --logInfo m!"{listV},{listHE}"

  logInfo m!"{← listV.mapM (fun e =>  ppExpr e)}"
  logInfo m!"{← listH.mapM (fun e =>  (ppExpr e.1)) }"
  logInfo m!"{← listH.mapM (fun e =>  (ppExpr e.2.1)) }"
  logInfo m!"{← listH.mapM (fun e =>  (ppExpr e.2.2)) }"

  let n := listV.length
  let nQ : Q(Nat) := Expr.lit (Literal.natVal n)
  let J : Q(Type) := mkApp q(Fin) nQ

  let QuivJ ← mkAppM ``QuivJ #[nQ, QuivJE]
  let instQuiver ← mkAppOptM ``Quiver.mk #[J, QuivJ]

  let FunObj ← mkAppOptM `ObjMapJ #[listVE]

  --FunMapJ : (a b : Cate) (e : List (a ⟶ b)) (n : ℕ) (h : List (List ℕ)) (x y : Fin n) (hyp : (--- = ---)
  --let FunMap ← mkAppM `FunMapJ #[]


  evalTactic <| ← `(tactic| set $(mkIdent "J".toName) := $(← Term.exprToSyntax J))
  evalTactic <| ← `(tactic| set $(mkIdent "JQ".toName) := $(← Term.exprToSyntax instQuiver))
  evalTactic <| ← `(tactic| set $(mkIdent "Jfun".toName) := $(← Term.exprToSyntax FunObj))
  --evalTactic <| ← `(tactic| set $(mkIdent "Diag".toName) := CST `C x)

  --let v := sorry
  --let e := sorry

  --let D := sorry

  --return-/



example {a b c d : Cate} (f h : a ⟶ b) (g : c ⟶ b) : True := by
  let v: List Cate := [a, b, c]
  let e (a b : Fin 3) : List (v.get a ⟶ v.get b) := match a,b with
    |0,1 => [f]
    |2,1 => [g]
    | _,_ => []

  let J := Fin 3
  let JQ : Quiver J := Quiver.mk <| QuivJ v e
  let JDiag : J ⥤q Cate := ⟨ObjMapJ v , FunMapJ v e⟩

  have : JDiag.obj 1 = b := by rfl
  have : JDiag.map (⟨0, by simp [toNb,e, v] ⟩ : JQ.Hom 0 1 ) = f := by rfl


  BuildDiagram
  --suffices : Jfun ⟨0, sorry⟩ = Jfun ⟨0,sorry⟩
  --exact this


  let x : Fin 4 := ⟨2,by exact Nat.lt_of_sub_eq_succ rfl⟩

  let JDiag : J ⥤q Cate := ⟨ Jfun, by
    intro x y hom


    sorry⟩

  have : JDiag.obj x  = c := by
    rfl
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

#expr [e2]

variable (x : C)

#expr [x]
#expr [Prefunctor (Fin 4) (Fin 4)]



def CST : Prefunctor J C where
  obj _ := x
  map _ := 𝟙 x

#expr [CST]
