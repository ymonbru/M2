import Mathlib
import Qq

open Qq Lean Meta Elab Tactic CategoryTheory

universe u v

variable {Cate: Type u} [Quiver.{v+1,u} Cate] -- in order to allow the lemmas used by the tactic to work, there is ne need of the +1.

/-- Intermediate function (it will be aplied into a List.foldr) that store a list of Expr and add e if it's definitionaly equal to an element of type cat-/
def isObjStep (cat : Expr) (e : Expr) (l : List Expr) : TacticM <| List Expr := do
  if ← isDefEq (← inferType e) cat  then
    return e :: l
  else
    return l

/-- Intermediate function (it will be aplied into a List.foldr) that store a list of morphisms and add e if it's definitionaly equal to an element of type cat-/
def isHomStep (cat : Expr) (e : Expr) (l : List <| Expr × Expr × Expr) : TacticM <|  List <| Expr × Expr × Expr := do
  let typeE ← inferType e
  let x ←  mkFreshExprMVar cat
  let y ←  mkFreshExprMVar cat
  let h ← mkAppOptM ``Quiver.Hom #[cat, none, x, y]
  if ← isDefEq typeE h then
    return ⟨e,x,y⟩ :: l
  else
    return l

/-- Takes an element of type Fin n and give the coresponding expression. Probably very ackward at the moment-/
def mkFinE {n : Nat} (x : Fin n) : TacticM Expr := do
  let nQ : Q(Nat) := Expr.lit (Literal.natVal n)
  let xQ : Q(Nat) := Expr.lit (Literal.natVal x.val)

  -- vraiment pas ouf du tout mais on verra mieux plus tard
  let ineq  ← mkAppM ``LT.lt #[xQ,nQ]
  let newGoal ← mkFreshExprMVar ineq
  appendGoals [newGoal.mvarId!]
  evalTactic <| ← `(tactic| rotate_left; repeat decide)
  mkAppM ``Fin.mk #[xQ, newGoal]

/- the variables that will be Meta-Computed by the tactic. -/
variable {v : List Cate} (l : List <| Σ a b : Fin v.length, v.get a ⟶ v.get b)

/-- If a morphism is represented as (f,a,b) with f: a⟶ b, it gives (f, k, n) where k and n are the positions of a and b in vE-/
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

/-- takes a morphism and a family of lists of morphisms and add the morphism to the list of morphism of the same type. Very awckward at the moment.-/
def baseE (f :  Σ a b : Fin v.length, v.get a ⟶ v.get b) (e : Π a b : Fin v.length, List (v.get a ⟶ v.get b)): Π a b : Fin v.length, List (v.get a ⟶ v.get b) := fun a b =>
  if h: a = f.1 ∧ b = f.2.1 then
    (Quiver.homOfEq f.2.2 (by rw[h.1]) (by rw [h.2])) :: e a b
  else
    e a b
/-- Build the familly of all the morphism in the context as a pi-type.-/
def e : Π a b : Fin v.length, List (v.get a ⟶ v.get b) :=
  List.foldr baseE (fun _ _ => []) l

/-- Gives the "Matrix" containing the number of morphisms of type v i ⟶ vj in the context-/
def toNb : List <| List Nat := List.ofFn (fun x => List.ofFn (fun k => (e l x k).length))

/-- The instance of Quiver build on Fin v.length: the morphisms between and i and j are Fin number of morphisms between v i and v j in the context-/
def QuivJ (x y : Fin v.length): Type :=
  let h := toNb l
  let a : Fin h.length := ⟨x.val, Fin.val_lt_of_le x (le_of_eq (by simp [h,toNb]))⟩
  let b : Fin (h.get a).length := ⟨y.val, Fin.val_lt_of_le y (le_of_eq (by simp [h, a, toNb]))⟩

  Fin <| ((h.get a).get b)

/-- The object map of the prefunctor-/
def ObjMapJ : Fin v.length → Cate := v.get

/-- the function map of the prefunctor-/
def FunMapJ  {x y : Fin v.length} (f : QuivJ l x y) : (ObjMapJ x ⟶ ObjMapJ y) := (e l x y).get ⟨f.val, Fin.val_lt_of_le f (le_of_eq (by simp [toNb]))⟩

/-- An helper to build a morphism of the good type. It will be used to build expressions.-/
def mkSigma (x y : Fin v.length) (f : v.get x ⟶ v.get y) : Σ a b : Fin v.length, v.get a ⟶ v.get b := Sigma.mk x (Sigma.mk y f)

/-- Version of the same function but adapted to Expr-/
def mkSigmaE (v : Expr) (f : Expr × Expr × Expr) : TacticM Expr := do
  mkAppOptM ``mkSigma #[none, none, v, f.2.1, f.2.2, f.1]

/-- Takes a list of Expr (coresponding to elements of type t in the context) and gives the Expr coresponding to it-/
def consE (l : List Expr) (t : Expr) : TacticM Expr := do
  let nil ← mkAppOptM ``List.nil #[t]
  List.foldrM (fun e l => mkAppM ``List.cons #[e, l]) nil l

/-- An helper to define the Expr coresponding to this type-/
def mkTypeAux (l : List Cate) : Type v := (Σ a b : Fin l.length, List.get l a ⟶ List.get l b)

def replace (a : Expr) (e : Expr) : MetaM Expr := do logInfo m!"{a}";match e with
  |.bvar _ => return e
  |.fvar _ => if ← isDefEq e a then return a else return e
  |.mvar _ => return e
  |.sort _ => return e
  |.const _ _ => if ← isDefEq e a then return a else return e
  |.app fn arg => return .app (← replace a fn) (← replace a arg)
  |.lam binderName binderType body binderInfo => return .lam binderName (← replace a binderType) (← replace a body) binderInfo
  |.forallE binderName binderType body binderInfo => return .forallE binderName (← replace a binderType) (← replace a body) binderInfo
  |.letE declName type value body nondep => return .letE declName (← replace a type) (← replace a value) (← replace a body) nondep
  |.lit _ => return e
  |.mdata _ _ => return e
  |.proj typeName idx struct => return .proj typeName idx (← replace a struct)

  --|_ => e

/-- Build the Expr of the diagram (and the instance of quiver on the source, it will be needed)-/
def BuildDiagram (cat : Q(Type)) : TacticM <| Expr × Expr := do
  -- get the Expr corespongind to the instance of category of $cat
  let uQ ← mkFreshLevelMVar
  let vQ ← mkFreshLevelMVar
  --pas beau du tout mais on verra après
  let QuivCat := Expr.app (Expr.const `Quiver [vQ, uQ]) cat
  let newGoal ← mkFreshExprMVar QuivCat
  appendGoals [newGoal.mvarId!]
  evalTactic <| ← `(tactic| rotate_left;infer_instance)

  let hyp ← getLocalHyps --NB : this does not grab the elements defined before applying the tactic.

  -- Get the list of objects in the context (as Expr)
  let listV ←  Array.foldrM (isObjStep cat) [] hyp
  let listVE : Q(List $cat) ← consE listV cat

  --logInfo m!"{listV}"
  --logInfo m!"{ (← (replace listV[0]! (← getMainTarget) ))}"

  -- Get the list of morphisms in the context (as Expr)
  let listH ←  Array.foldrM (isHomStep cat) [] hyp
  --logInfo m!"{listH}"
  let listH ← listH.mapM (mkHomNum cat listV)
  let listH ← listH.mapM (mkSigmaE listVE)
  let t ← mkAppM ``mkTypeAux #[listVE]
  let listHE ← consE listH.reverse t

  -- Build the Expr of the index Quiver of the diagram
  let n := listV.length
  let nQ : Q(Nat) := Expr.lit (Literal.natVal n)
  let J : Q(Type) := mkApp q(Fin) nQ

  -- Build the Quiver instance over J
  let QuivJ ← mkAppOptM ``QuivJ #[none, none, listVE, listHE]
  let instQuiverJ ← mkAppOptM ``Quiver.mk #[J, QuivJ]

  --Build the diagram
  let FunObjJ ← mkAppOptM ``ObjMapJ #[none, listVE]
  let FunMapJ ← mkAppOptM ``FunMapJ #[none, none, listVE, listHE]
  let DiagJ ← mkAppOptM ``Prefunctor.mk #[J,instQuiverJ, cat, newGoal , FunObjJ, FunMapJ ]
  --let Diag ← mkAppOptM ``Paths.lift #[J, instQuiverJ, none, none, DiagJ]

  return ⟨instQuiverJ, DiagJ⟩


/-- The tactic that build the diagram. The objects and morphism will be definitionaly equal to the one in the context.-/
elab "BuildDiagram_of" c:term : tactic => do
  let cat : Q(Type) ← Term.elabTerm c none

  let ⟨instQuiverJ, DiagJ⟩ ← BuildDiagram cat

  --Add the diagram to the context
  --evalTactic <| ← `(tactic| set $(mkIdent `J) : Type := $(← Term.exprToSyntax J))
  evalTactic <| ← `(tactic| set $(mkIdent "QuivJ".toName) := $(← Term.exprToSyntax instQuiverJ))
  evalTactic <| ← `(tactic| set $(mkIdent "Diag".toName) := $(← Term.exprToSyntax DiagJ))

variable (C2: Type u) [Quiver.{v+1,u} C2]

example {x y : C2} (X : AlgebraicGeometry.Scheme) (k : x ⟶ y) {a b c d : Cate} (h f: a ⟶ b) (g : c ⟶ b) : a = a ∧ 1=2 := by
  let x : Cate := a
  suffices x = a ∧ 1=2 by
    exact this

  BuildDiagram_of Cate

  ---rename a => Diag.obj 0





  --BuildDiagram_of C2
  --BuildDiagram_of AlgebraicGeometry.Scheme

  have : Diag.obj 1 = b := by rfl
  have : Diag.map (⟨0, by simp [toNb, mkSigma, e, baseE ]⟩ : QuivJ.Hom 0 1 ) = f := by rfl

  --simp

  sorry
