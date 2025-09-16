import Mathlib
--import Mathlib.Tactic.Localise

universe v u

--attribute [aesop apply unsafe (rule_sets := [Localise])] AlgebraicGeometry.IsLocalAtTarget.of_openCover

open AlgebraicGeometry CategoryTheory

section

variable {P Q : MorphismProperty Scheme.{u}} {X Y : Scheme.{u}} (f : X ⟶ Y)

--@[aesop apply unsafe 1% (rule_sets := [Localise])]
lemma AlgebraicGeometry.IsLocalAtTarget.of_affineCover [IsLocalAtTarget P] (_ : ¬ IsAffine Y)
    (H : ∀ i, P (Scheme.Cover.pullbackHom Y.affineCover f i)) : P f :=
  IsLocalAtTarget.of_openCover Y.affineCover H

--@[aesop apply unsafe 1% (rule_sets := [Localise])]
lemma AlgebraicGeometry.IsLocalAtSource.of_affineCover [IsLocalAtSource P] (_ : ¬ IsAffine X)
    (H : ∀ i, P (X.affineCover.map i ≫ f)) : P f :=
  IsLocalAtSource.of_openCover X.affineCover H

--@[aesop apply unsafe 50% (rule_sets := [Localise])]
lemma AlgebraicGeometry.IsLocalAtTarget.pullbackHom [IsLocalAtTarget P] (𝒰 : Y.OpenCover)
    (hf : P f) (i : 𝒰.J) : P (𝒰.pullbackHom f i) :=
  (IsLocalAtTarget.iff_of_openCover 𝒰).mp hf i

--@[aesop apply unsafe 50% (rule_sets := [Localise])]
lemma AlgebraicGeometry.IsLocalAtSource.precomp [IsLocalAtSource P] (𝒰 : X.OpenCover)
    (hf : P f) (i : 𝒰.J) : P (𝒰.map i ≫ f) :=
  IsLocalAtSource.comp hf _

--add_aesop_rules unsafe 1% [(by infer_instance) (rule_sets := [Localise])]

section

--@[aesop apply unsafe 1% (rule_sets := [Localise])]
lemma foo_of_isAffine [IsAffine X] [IsAffine Y] (H : P f) : Q f :=
  sorry

variable [IsLocalAtTarget P] [IsLocalAtTarget Q] [IsLocalAtSource P] [IsLocalAtSource Q]

set_option maxHeartbeats 0 in
lemma foo (H : P f) : Q f := by
  wlog hY : IsAffine Y generalizing X Y f
  · sorry
  --wlog hX : IsAffine X generalizing X f
  --· localise
  --exact foo_of_isAffine f H
  sorry

end

end

section

variable {J : Type*} [Category J]

class Localisor (i : J) where
  localiseAt (D : J ⥤ Scheme.{u}) {U : Scheme.{u}} (f : U ⟶ D.obj i) : J ⥤ Scheme.{u}

instance : Localisor (false : Bool) where
  localiseAt D {U} f :=
    { obj x := match x with
        | .false => U
        | .true => D.obj true
      map {x y} g := match x, y with
        | .true, .true => 𝟙 _
        | .false, .true => f ≫ D.map g
        | .false, .false => 𝟙 _
      map_comp {x y z} u v := by
        split
        · rfl
        · simp only [Category.assoc]
          cases z
          · simpa using Bool.eq_true_of_true_le (leOfHom v)
          · rfl
        · rfl }

def CategoryTheory.Functor.localiseAt (i : J) [Localisor i] (D : J ⥤ Scheme.{u}) {U}
    (f : U ⟶ D.obj i) : J ⥤ Scheme.{u} :=
  Localisor.localiseAt D f

@[simp]
lemma localiseAt_false (D : Bool ⥤ Scheme.{u}) {U} (f : U ⟶ D.obj false) :
    (D.localiseAt false f).obj false = U :=
  rfl

example (P : (J ⥤ Scheme.{u}) → Prop) (D : J ⥤ Scheme.{u}) (hD : P D) : True := by
  sorry

class IsLocalAt (P : (J ⥤ Scheme.{u}) → Prop) (i : J) [Localisor i] : Prop where
  iff_of_openCover (D : J ⥤ Scheme.{u}) (𝒰 : Scheme.OpenCover.{u} (D.obj i)) :
   P D ↔ ∀ j : 𝒰.J, P (D.localiseAt i (𝒰.map j))

--set_option pp.universes true
lemma CategoryTheory.Functor.of_openCover (P : (J ⥤ Scheme.{u}) → Prop) (i : J) [Localisor i]
    [IsLocalAt P i] (D : J ⥤ Scheme.{u}) (𝒰 : Scheme.OpenCover.{u} (D.obj i))
    (H : ∀ j : 𝒰.J, P (D.localiseAt i (𝒰.map j))) :
    P D :=
  (IsLocalAt.iff_of_openCover D 𝒰).mpr H

--set_option pp.universes true
lemma CategoryTheory.Functor.iff_of_openCover (P : (J ⥤ Scheme.{u}) → Prop) (i : J) [Localisor i]
    (D : J ⥤ Scheme.{u}) (𝒰 : Scheme.OpenCover.{u} (D.obj i)) [IsLocalAt P i] :
    P D ↔ ∀ j : 𝒰.J, P (D.localiseAt i (𝒰.map j)) :=
  IsLocalAt.iff_of_openCover D 𝒰

lemma CategoryTheory.Functor.localiseAt_map (P : (J ⥤ Scheme.{u}) → Prop) (i : J) [Localisor i]
    (D : J ⥤ Scheme.{u}) (𝒰 : Scheme.OpenCover.{u} (D.obj i)) [IsLocalAt P i]
    (j : 𝒰.J) (H : P D) :
    P (D.localiseAt i (𝒰.map j)) :=
  (D.iff_of_openCover P i 𝒰).mp H j

open Lean Elab Meta Tactic

open Qq
def localiseGoals (goal : MVarId) (idx : Expr) : TacticM (List MVarId) := do
  goal.withContext do
  goal.checkNotAssigned `wlog
  let goalType ← goal.getType
  let headExpr := goalType.getAppFn
  let args := goalType.getAppArgs
  let diagrams ← args.filterM <| fun expr => do
    let ty ← inferType expr
    match ty.getAppFn with
    | .const ``CategoryTheory.Functor _ => return true
    | _ => return false
  let lctx := (← goal.getDecl).lctx
  let diagramVars ← lctx.getFVars.filterMapM fun fvar => do
    let ty ← inferType fvar
    match ty.getAppFn with
    | .const ``CategoryTheory.Functor _ =>
      return some (lctx.fvarIdToDecl.find! fvar.fvarId!).userName
    | _ => return none
  logInfo s!"{diagramVars}"
  let D : Expr := diagrams[0]!
  let stxD : TSyntax `ident ← `(ident|$(mkIdent diagramVars[0]!))
  let X : Expr ← mkAppM ``Prefunctor.obj #[← mkAppM ``CategoryTheory.Functor.toPrefunctor #[D], idx]
  let 𝒰 : Expr ← mkAppM ``Scheme.affineCover #[X]
  logInfo s!"{𝒰}"
  let P : Expr ← mkAppM ``IsAffine #[X]
  let ⟨reductionGoal, ⟨H, _negHyp⟩, hypothesisGoal, _, _⟩ ← goal.wlog `h P (some #[stxD]) `H
  let redGoals ← reductionGoal.withContext do
    let target ← reductionGoal.getType
    let app ← mkAppM ``CategoryTheory.Functor.of_openCover #[headExpr, idx, D, 𝒰]
    let appTy ← inferType app
    let (args, _, conclusion) ← forallMetaTelescopeReducing appTy
    if ← isDefEq target conclusion then
      reductionGoal.assign (mkAppN app args)
      --logInfo s!"{((← reductionGoal.getDecl).lctx.fvarIdToDecl.find! H).userName}"
      let newGoals ← args.filterMapM fun mvar => do
        let mvarId := mvar.mvarId!
        if (← mvarId.isAssigned) || (← mvarId.isDelayedAssigned) then return none
        -- intro the index of the cover
        let (_, mvarId) ← mvarId.introNP 1
        return mvarId
        --let HType ← inferType (.fvar H)
        --let (args', _, _conclusion') ← forallMetaTelescopeReducing HType
        --mvarId.assign (mkAppN (.fvar H) args')
        --let newGoals' ← args'.filterMapM fun mvar => do
        --  let mvarId : MVarId := mvar.mvarId!
        --  if (← mvarId.isAssigned) || (← mvarId.isDelayedAssigned) then return mvarId
        --  else return mvarId
        --return some newGoals'
        --if ← isDefEq target' conclusion' then
        --  return none
        --else
        --  return some mvarId
      --return newGoals.toList
      match newGoals with
      | #[newGoal] =>
        newGoal.withContext do
        let target' ← newGoal.getType
        let HType ← inferType (.fvar H)
        let (args', _, conclusion') ← forallMetaTelescopeReducing HType
        --let newGoals' ← args'.filterMapM fun mvar => do
        --  let mvarId : MVarId := mvar.mvarId!
        --  if (← mvarId.isAssigned) || (← mvarId.isDelayedAssigned) then return mvarId
        --  else return mvarId
        logInfo s!"{← ppExpr target'} vs {← ppExpr conclusion'}"
        if ← isDefEq target' conclusion' then
          newGoal.assign (mkAppN (.fvar H) args')
          let newGoals ← args'.filterMapM fun mvar => do
            let mvarId : MVarId := mvar.mvarId!
            if (← mvarId.isAssigned) || (← mvarId.isDelayedAssigned) then return none
            else return mvarId
          return newGoals.toList
        --  return []
        else
          logInfo "does not match"
          return [newGoal]
      | ls =>
        logInfo "Produced too many side goals."
        return ls.toList
    else
      return []
  return redGoals ++ [hypothesisGoal]

--open private withFreshCache mkAuxMVarType from Lean.MetavarContext in
elab "localiseAt" i:term : tactic => do
  withMainContext do
  let goal ← getMainGoal
  let expr ← elabTerm i none
  replaceMainGoal (← localiseGoals goal expr)

example (P Q : (Bool ⥤ Scheme.{u}) → Prop) [IsLocalAt P false] [IsLocalAt Q false]
    (D : Bool ⥤ Scheme.{u}) (hD : P D) : Q D := by
  localiseAt false-- using (D.obj false).affineCover
  · sorry
  · dsimp; infer_instance
  · sorry
  --wlog h : IsAffine (D.obj false) generalizing D
  --· rw [D.iff_of_openCover Q false (D.obj false).affineCover]
  --  intro j
  --  apply this (D.localiseAt false _)
  --  · exact D.localiseAt_map P false _ _ hD
  --  · dsimp only [localiseAt_false]
  --    infer_instance
  --sorry

variable {V : Type*} [Quiver V]

structure FromList {α : Type*} (l : List α) : Type where
  obj : Fin l.length

instance {α : Type*} (l : List α) : BEq (FromList l) where
  beq x y := x.obj == y.obj

instance {α : Type*} (l : List α) : LawfulBEq (FromList l) := sorry

instance {α : Type*} (l : List α) : Hashable (FromList l) where
  hash x := hash x.obj

elab "constructDiag" : tactic => do
  withMainContext do
  let goal ← getMainGoal
  let lctx := (← goal.getDecl).lctx
  let objs : List FVarId ← lctx.getFVars.toList.filterMapM fun fvar => do
    let id := fvar.fvarId!
    let ty ← inferType fvar
    match ty.getAppFn with
    | .const ``AlgebraicGeometry.Scheme _ => return id
    | _ => return none
  let objsE : Q(List Scheme.{0}) ←
    objs.foldrM (fun fvar ex ↦ mkAppM ``List.cons #[.fvar fvar, ex]) q([])
  let homsE : Q(Std.DHashMap (FromList $objsE × FromList $objsE)
      (fun p => List ($objsE[p.1.obj] ⟶ $objsE[p.2.obj]))) ←
    lctx.getFVars.foldrM (init := q(.emptyWithCapacity)) fun fvar map => do
      let id := fvar.fvarId!
      let ty ← inferType fvar
      match ty.getAppFn with
      | .const ``Quiver.Hom _ =>
        let args := ty.getAppArgs
        -- this assumes that all domains / codomains are free variables (!)
        let lhs := args[2]!.fvarId!
        let rhs := args[3]!.fvarId!
        match List.finIdxOf? lhs objs, List.finIdxOf? rhs objs with
        | some i, some j =>
          let lhsI : Q(Fin (List.length $objsE)) ←
            mkAppM ``Fin.mk #[q($i.1), q($i.2)]
          let rhsI : Q(Fin (List.length $objsE)) ←
            mkAppM ``Fin.mk #[q($j.1), q($j.2)]
          let p : Q(FromList $objsE × FromList $objsE) :=
            q((FromList.mk $lhsI, FromList.mk $rhsI))
          let f : Q($objsE[$p.1.obj] ⟶ $objsE[$p.2.obj]) := .fvar id
          let upd : Q(Option (List ($objsE[$p.1.obj] ⟶ $objsE[$p.2.obj])) →
              Option (List ($objsE[$p.1.obj] ⟶ $objsE[$p.2.obj]))) :=
            q(fun x ↦ match x with
                | some ls => $f :: ls
                | none => [$f])
          mkAppM ``Std.DHashMap.alter #[map, p, upd]
        | _, _ => return map
      | _ => return map
  let J₀ : Q(Type) := q(FromList $objsE)
  let instQuiver : Q(Quiver.{1, 0} $J₀) :=
    q({ Hom i j := FromList (Std.DHashMap.getD $homsE (i, j) []) })
  let J : Q(Type) := q(Paths $J₀)
  -- construct object part of prefunctor
  let objFun : Expr ← withLocalDecl `j BinderInfo.default J fun j => do
    let body ← mkAppM ``List.get #[objsE, ← mkAppM ``FromList.obj #[j]]
    mkLambdaFVars #[j] body
  -- construct map part of prefunctor
  let homFun : Expr ← withLocalDecl `i BinderInfo.implicit J fun i => do
    withLocalDecl `j BinderInfo.implicit J fun j => do
      let instCat : Expr ← mkAppOptM ``Paths.categoryPaths #[J₀, instQuiver]
      let instQuiverJ : Expr ← mkAppOptM ``CategoryStruct.toQuiver
        #[none, ← mkAppOptM ``Category.toCategoryStruct #[none, instCat]]
      let ty : Expr ← mkAppOptM ``Quiver.Hom #[J₀, instQuiver, i, j]
      withLocalDecl `f BinderInfo.default ty fun f => do
        let i : Q(FromList $objsE) := i
        let j : Q(FromList $objsE) := j
        let p : Q(FromList $objsE × FromList $objsE) ←
          mkAppM ``Prod.mk #[i, j]
        let lhs : Q(Scheme.{0}) ← mkAppM ``List.get #[objsE, ← mkAppM ``FromList.obj #[i]]
        let rhs : Q(Scheme.{0}) ← mkAppM ``List.get #[objsE, ← mkAppM ``FromList.obj #[j]]
        let lstExpr : Expr := q((Std.DHashMap.getD $homsE ($i, $j) []))
        let f : Q(FromList (Std.DHashMap.getD $homsE ($i, $j) [])) := f
        let body ← mkAppM ``List.get #[lstExpr, ← mkAppOptM ``FromList.obj #[none, lstExpr, f]]
        mkLambdaFVars #[i, j, f] body
  -- the prefunctor obtained from `objFun` and `homFun`
  let Dp : Expr ← mkAppOptM ``Prefunctor.mk #[J₀, instQuiver, q(Scheme.{0}), none, objFun, homFun]
  -- the induced functor from the path category
  let D : Expr ← mkAppOptM ``Paths.lift #[J₀, instQuiver, none, none, Dp]
  liftMetaTactic fun goal => do
    -- add `D` to the context (with definition)
    let (_, goal) ← (← goal.define `D (← inferType D) D).intro1P
    -- add the quiver instance to the context (with definition)
    let (_, goal) ← (← goal.define `instQuiver (← inferType instQuiver) instQuiver).intro1P
    return [goal]

structure GraphData (goal : MVarId) where
  objs : List FVarId
  idx : Std.HashMap FVarId (FromList objs)
  outward : Std.HashMap FVarId (List <| FVarId × FVarId)
  inward : Std.HashMap FVarId (List <| FVarId × FVarId)
  homs : Std.HashMap (FromList objs × FromList objs) (List FVarId)
  homsMap : Std.DHashMap ((FromList objs × FromList objs) × FVarId)
    (fun p => FromList (homs.getD p.1 []))
  homs' : FromList objs → FromList objs → List FVarId
  --homObjs : Std.HashMap FVarId (FromList objs × FromList objs)
  -- homMap : Std.DHashMap FVarId (fun id ↦ homObjs.getD _)

--def GraphData.curriedHom {goal : MVarId} (g : GraphData goal) :
--    Std.HashMap (FVarId × FVarId) (List FVarId) := Id.run <| do
--  let mut map := .emptyWithCapacity
--  for (lhs, ls) in g.outward do
--    for (rhs, hom) in ls do
--      continue
--  return map

/-- The outward corners of a graph data are the vertices with no incoming edges. -/
def GraphData.outCorners {goal : MVarId} (g : GraphData goal) : List FVarId :=
  g.objs.filter (fun fvar ↦ !g.inward.contains fvar)

/-- The inward corners of a graph data are the vertices with no outgoing edges. -/
def GraphData.inCorners {goal : MVarId} (g : GraphData goal) : List FVarId :=
  g.objs.filter (fun fvar ↦ !g.outward.contains fvar)

def GraphData.sourceLocalisable {goal : MVarId} (g : GraphData goal) : List FVarId :=
  g.outCorners

def List.insertOption {α : Type*} (a : α) : Option (List α) → List α
  | none => [a]
  | some ls => a :: ls

def constructGraphData (goal : MVarId) : TacticM (GraphData goal) := do
  let lctx := (← goal.getDecl).lctx
  let objs : List FVarId ← lctx.getFVars.toList.filterMapM fun fvar => do
    let id := fvar.fvarId!
    let ty ← inferType fvar
    match ty.getAppFn with
    | .const ``AlgebraicGeometry.Scheme _ => return id
    | _ => return none
  let mut outward : Std.HashMap FVarId (List <| FVarId × FVarId) := .emptyWithCapacity
  let mut inward : Std.HashMap FVarId (List <| FVarId × FVarId) := .emptyWithCapacity
  let mut homs : Std.HashMap (FromList objs × FromList objs) (List FVarId) := .emptyWithCapacity
  let mut idx : Std.HashMap FVarId (FromList objs) := .emptyWithCapacity
  for i in List.finRange objs.length do
    idx := idx.insert (objs.get i) ⟨i⟩
  for fvar in lctx.getFVars do
    let id := fvar.fvarId!
    let ty ← inferType fvar
    match ty.getAppFn with
    | .const ``Quiver.Hom _ =>
      let args := ty.getAppArgs
      -- this assumes that all domains / codomains are free variables (!)
      let lhs := args[2]!.fvarId!
      let rhs := args[3]!.fvarId!
      outward := outward.alter lhs (fun l ↦ some <| .insertOption (rhs, id) l)
      inward := inward.alter rhs (fun l ↦ some <| .insertOption (lhs, id) l)
      match List.finIdxOf? lhs objs, List.finIdxOf? rhs objs with
      | some i, some j => homs := homs.alter (⟨i⟩, ⟨j⟩) (fun l ↦ some <| .insertOption id l)
      | _, _ => continue
    | _ => continue
  let mut homsMap : Std.DHashMap ((FromList objs × FromList objs) × FVarId)
      (fun p => FromList (homs.getD p.1 [])) := .emptyWithCapacity
  for (p, l) in homs do
    for i in List.finRange l.length do
      let fvar := l[i]
      homsMap := homsMap.insert (p, fvar) ⟨⟨i, sorry⟩⟩
  let homs' (i j : FromList objs) : List FVarId := homs.getD (i, j) []
  return ⟨objs, idx, outward, inward, homs, homsMap, homs'⟩

def GraphData.objsE {goal : MVarId} (g : GraphData goal) : MetaM Q(List Scheme.{0}) :=
  letI X (fvar : FVarId) : Q(Scheme.{0}) := .fvar fvar
  return g.objs.foldr (fun fvar ex ↦ q($(X fvar) :: $ex)) q([])

def Lean.mkFinEx {n : ℕ} (i : Fin n) : Q(Fin $n) := q($i)

def Lean.mkListEx (u : Level) (α : Q(Type u)) : List Q($α) → Q(List $α)
  | [] => q([])
  | e :: es => q($e :: $(mkListEx u α es))

def GraphData.homsE {goal : MVarId} (g : GraphData goal) : MetaM Expr := do
  let objsE : Q(List Scheme.{0}) ← g.objsE
  let homsE : Q(Std.DHashMap (FromList $objsE × FromList $objsE)
      (fun p => List (List.get $objsE p.1.obj ⟶ List.get $objsE p.2.obj))) ←
    g.homs.foldM (init := q(.emptyWithCapacity)) fun expr p hs => do
      let lhsI : Q(Fin (List.length $objsE)) := mkFinEx p.1.obj
      let rhsI : Q(Fin (List.length $objsE)) := mkFinEx p.2.obj
      let p : Q(FromList $objsE × FromList $objsE) := q((⟨$lhsI⟩, ⟨$rhsI⟩))
      let ty ← mkAppM ``Quiver.Hom
        #[← mkAppM ``List.get #[objsE, lhsI], ← mkAppM ``List.get #[objsE, rhsI]]
      mkAppM ``Std.DHashMap.insert
        #[expr, p, mkListEx 0 ty (hs.map (.fvar ·))]
  return homsE

--def Lean.Expr.get

--def FromList.mkExprQ {u v : Level} {α : Q(Type u)} {β : Q(Type v)}
--    {l : Q(List $α)} (elems : FromList $l →

@[inline]
abbrev FromList.ofFinFun {α β : Type*} {l : List α} (f : Fin l.length → β) : FromList l → β :=
  fun i ↦ f i.obj

--#check toExpr
--def FromList.mkExpr {α : Type u} {β : Type v} [ToLevel.{u}] [ToLevel.{v}]
--      [ToExpr α] [ToExpr β] (l : List α) : ToExpr (FromList l → β) :=
--  have lu := toLevel.{u}
--  have lv := toLevel.{v}
--  have eα : Q(Type $lu) := toTypeExpr α
--  have eβ : Q(Type $lv) := toTypeExpr β
--  let el : Q(List $eα) := toExpr l
--  let toTypeExpr := q(FromList $el → $eβ)
--  { toTypeExpr,
--    toExpr v :=
--      let v' : Fin l.length → β := fun i ↦ v (FromList.mk i)
--      --let en : Q(Nat) := q($(List.length l))
--      let expr : Q(Fin (List.length $el) → $eβ) := toExpr v'
--      --let expr' : Q(FromList $el → $eβ) :=
--      --  q(fun i ↦ _)
--      q(FromList.ofFinFun $expr)
--    }

def GraphData.homsE' {goal : MVarId} (g : GraphData goal) : MetaM Expr := do
  let objsE : Q(List Scheme.{0}) ← g.objsE
  let J₀ : Q(Type) := q(FromList $objsE)
  let f := g.homs'
  --let expr :
  --    Q((i : FromList $objsE) → (j : FromList $objsE) → List ($objsE[i.obj] ⟶ $objsE[j.obj])) :=
  --  q(fun i j ↦ _)
  withLocalDecl `i BinderInfo.default J₀ fun i => do
    withLocalDecl `j BinderInfo.default J₀ fun j => do
      let body : Expr ← do
        logInfo s!"{i.isFVar} {j.isFVar}"
        --mkListEx 0 q(Nat) []
        /- This does not work, because `i` and `j` are free variables here. -/
        match i, j with
        | Expr.app
            (.app (.app (.const ``FromList.mk [0]) _) (.app _ _))
            (.app (.app (.app (.const ``Fin.mk []) _) (.lit <| .natVal n1)) pf1),
          Expr.app
            (.app (.app (.const ``FromList.mk [0]) _) (.app _ _))
            (.app (.app (.app (.const ``Fin.mk []) _) (.lit <| .natVal n2)) pf2) =>
          --let ty : Expr ← mkAppOptM ``Quiver.Hom #[J₀, instQuiver, i, j]
          let lhsE : Q(FromList $objsE) := i
          let rhsE : Q(FromList $objsE) := j
          --let foo : Q(FromList $objsE → FromList $objsE → List FVarId) := q(g.homs')
          let arg := g.homs' ⟨n1, sorry⟩ ⟨n2, sorry⟩
          let ty : Q(Type) ← mkAppM ``Quiver.Hom
            #[← mkAppM ``List.get #[objsE, lhsE], ← mkAppM ``List.get #[objsE, rhsE]]
          pure (mkListEx 0 ty (arg.map (.fvar ·)))
        | _, _ => pure (Expr.bvar 0)
      --let body : Q(List ()) : Expr := mkListEx 0 _ _
      -- let lstExpr : Expr := --q((Std.DHashMap.getD $homsE ($i, $j) []))
      --let f : Q(FromList (Std.DHashMap.getD $homsE ($i, $j) [])) := f
      --let body ← mkAppM ``List.get #[lstExpr, ← mkAppOptM ``FromList.obj #[none, lstExpr, f]]
      mkLambdaFVars #[i, j] body
  --let homsE : Expr
  --let homsE : Q((i : FromList $objsE) → (j : FromList $objsE)) ←
  --  g.homs.foldM (init := q(.emptyWithCapacity)) fun expr p hs => do
  --    let lhsI : Q(Fin (List.length $objsE)) := mkFinEx p.1.obj
  --    let rhsI : Q(Fin (List.length $objsE)) := mkFinEx p.2.obj
  --    let p : Q(FromList $objsE × FromList $objsE) := q((⟨$lhsI⟩, ⟨$rhsI⟩))
  --    let ty ← mkAppM ``Quiver.Hom
  --      #[← mkAppM ``List.get #[objsE, lhsI], ← mkAppM ``List.get #[objsE, rhsI]]
  --    mkAppM ``Std.DHashMap.insert
  --      #[expr, p, mkListEx 0 ty (hs.map (.fvar ·))]
  --return homsE

def GraphData.quiverE {goal : MVarId} (g : GraphData goal) : MetaM Expr := do
  let objsE : Q(List Scheme.{0}) ← g.objsE
  let J₀ : Q(Type) := q(FromList $objsE)
  let homsE' : Q(Std.DHashMap (FromList $objsE × FromList $objsE)
      (fun p => List (List.get $objsE p.1.obj ⟶ List.get $objsE p.2.obj))) ← g.homsE
  let instQuiver : Q(Quiver.{1, 0} $J₀) :=
    q({ Hom i j := FromList (Std.DHashMap.getD $homsE' (i, j) []) })
  return instQuiver

def GraphData.quiverE' {goal : MVarId} (g : GraphData goal) : MetaM Expr := do
  let objsE : Q(List Scheme.{0}) ← g.objsE
  let J₀ : Q(Type) := q(FromList $objsE)
  let homsE : Q((i : FromList $objsE) → (j : FromList $objsE) →
      List (List.get $objsE i.obj ⟶ List.get $objsE j.obj)) ← g.homsE'
  let instQuiver : Q(Quiver.{1, 0} $J₀) := q({ Hom i j := FromList ($homsE i j) })
  return instQuiver

def GraphData.catE {goal : MVarId} (g : GraphData goal) : MetaM Expr := do
  let objsE : Q(List Scheme.{0}) ← g.objsE
  let J₀ : Q(Type) := q(FromList $objsE)
  let instQuiver ← g.quiverE
  mkAppOptM ``Paths.categoryPaths #[J₀, instQuiver]

def GraphData.catE' {goal : MVarId} (g : GraphData goal) : MetaM Expr := do
  let objsE : Q(List Scheme.{0}) ← g.objsE
  let J₀ : Q(Type) := q(FromList $objsE)
  let instQuiver ← g.quiverE'
  mkAppOptM ``Paths.categoryPaths #[J₀, instQuiver]

def GraphData.functorE {goal : MVarId} (g : GraphData goal) : MetaM Expr := do
  let objsE : Q(List Scheme.{0}) ← g.objsE
  let J₀ : Q(Type) := q(FromList $objsE)
  let homsE : Q(Std.DHashMap (FromList $objsE × FromList $objsE)
      (fun p => List (List.get $objsE p.1.obj ⟶ List.get $objsE p.2.obj))) ← g.homsE
  -- construct object part of prefunctor
  let objFun : Expr ← withLocalDecl `j BinderInfo.default J₀ fun j => do
    let body ← mkAppM ``List.get #[objsE, ← mkAppM ``FromList.obj #[j]]
    mkLambdaFVars #[j] body
  let instQuiver ← g.quiverE
  -- construct map part of prefunctor
  let homFun : Expr ← withLocalDecl `i BinderInfo.implicit J₀ fun i => do
    withLocalDecl `j BinderInfo.implicit J₀ fun j => do
      let ty : Expr ← mkAppOptM ``Quiver.Hom #[J₀, instQuiver, i, j]
      withLocalDecl `f BinderInfo.default ty fun f => do
        let i : Q(FromList $objsE) := i
        let j : Q(FromList $objsE) := j
        let lstExpr : Expr := q((Std.DHashMap.getD $homsE ($i, $j) []))
        let f : Q(FromList (Std.DHashMap.getD $homsE ($i, $j) [])) := f
        let body ← mkAppM ``List.get #[lstExpr, ← mkAppOptM ``FromList.obj #[none, lstExpr, f]]
        mkLambdaFVars #[i, j, f] body
  -- the prefunctor obtained from `objFun` and `homFun`
  let Dp : Expr ← mkAppOptM ``Prefunctor.mk #[J₀, instQuiver, q(Scheme.{0}), none, objFun, homFun]
  -- the induced functor from the path category
  mkAppOptM ``Paths.lift #[J₀, instQuiver, none, none, Dp]

def GraphData.functorE' {goal : MVarId} (g : GraphData goal) : MetaM Expr := do
  let objsE : Q(List Scheme.{0}) ← g.objsE
  let J₀ : Q(Type) := q(FromList $objsE)
  let homsE : Q((i : FromList $objsE) → (j : FromList $objsE) →
      List (List.get $objsE i.obj ⟶ List.get $objsE j.obj)) ← g.homsE'
  logInfo "constructed homsE"
  let objFun : Expr ← withLocalDecl `j BinderInfo.default J₀ fun j => do
    let body ← mkAppM ``List.get #[objsE, ← mkAppM ``FromList.obj #[j]]
    mkLambdaFVars #[j] body
  logInfo "constructed objFun"
  let instQuiver ← g.quiverE'
  logInfo "constructed quiver"
  -- construct map part of prefunctor
  let homFun : Expr ← withLocalDecl `i BinderInfo.implicit J₀ fun i => do
    withLocalDecl `j BinderInfo.implicit J₀ fun j => do
      let ty : Expr ← mkAppOptM ``Quiver.Hom #[J₀, instQuiver, i, j]
      withLocalDecl `f BinderInfo.default ty fun f => do
        let i : Q(FromList $objsE) := i
        let j : Q(FromList $objsE) := j
        let lstExpr : Expr :=
          q(($homsE $i $j))
        let f : Q(FromList ($homsE $i $j)) := f
        let body ← mkAppM ``List.get #[lstExpr, ← mkAppOptM ``FromList.obj #[none, none, f]]
        logInfo "constructed body"
        mkLambdaFVars #[i, j, f] body
  logInfo "constructed homFun"
  -- the prefunctor obtained from `objFun` and `homFun`
  let Dp : Expr ← mkAppOptM ``Prefunctor.mk #[J₀, instQuiver, q(Scheme.{0}), none, objFun, homFun]
  -- the induced functor from the path category
  mkAppOptM ``Paths.lift #[J₀, instQuiver, none, none, Dp]

/-
def GraphData.localiseSourceAt {goal : MVarId} (g : GraphData goal)
    (i : FromList g.objs) (fvar : FVarId) :
    GraphData goal where
  objs := sorry
  idx := sorry
  outward := sorry
  inward := sorry
  homs := sorry
  homsMap := sorry
-/

def GraphData.functorObjE {goal : MVarId} {g : GraphData goal} (fvar : FVarId)
    (i : FromList g.objs) : MetaM Expr := do
  --let D : Expr ← g.functorE
  let objsE : Q(List Scheme.{0}) ← g.objsE
  let obj : Q(FromList $objsE) ← mkAppOptM ``FromList.mk #[none, objsE, mkFinEx i.obj]
  let instCat ← g.catE
  let instCatStruct ← mkAppOptM ``Category.toCategoryStruct #[none, instCat]
  let instQuiver ← mkAppOptM ``CategoryStruct.toQuiver #[none, instCatStruct]
  let D' : Expr ← mkAppOptM ``Functor.toPrefunctor #[none, instCat, none, none, Expr.fvar fvar]
  mkAppOptM ``Prefunctor.obj #[none, instQuiver, none, none, D', obj]

instance : LawfulBEq FVarId where
  rfl {x} := sorry
  eq_of_beq := sorry

def GraphData.functorMapE {goal : MVarId} {g : GraphData goal} (fvar : FVarId)
    (i j : FromList g.objs) (homId : FVarId) : MetaM Expr := do
  --let D : Expr ← g.functorE
  let objsE : Q(List Scheme.{0}) ← g.objsE
  let J₀ : Q(Type) := q(FromList $objsE)
  let homsE : Q(Std.DHashMap (FromList $objsE × FromList $objsE)
      (fun p => List (List.get $objsE p.1.obj ⟶ List.get $objsE p.2.obj))) ← g.homsE
  let instQuiverBase : Q(Quiver.{1, 0} $J₀) :=
    q({ Hom i j := FromList (Std.DHashMap.getD $homsE (i, j) []) })
  let fid := g.homsMap.getD ((i, j), homId) ⟨⟨0, sorry⟩⟩
  let i : Q(Fin (List.length $objsE)) := mkFinEx i.obj
  let j : Q(Fin (List.length $objsE)) := mkFinEx j.obj
  let i : Q(FromList $objsE) := q(FromList.mk $i)
  let j : Q(FromList $objsE) := q(FromList.mk $j)
  let fidNatE : Q(ℕ) := toExpr fid.obj.1
  let natE : Q(ℕ) := q(List.length (Std.DHashMap.getD $homsE ($i, $j) []))
  --let pf : Expr := ← do
  --  let pf' : Q($fidNatE < $natE) := sorry
  --  return pf'
  let fid' : Expr := mkFinEx fid.obj
    --mkAppOptM ``Fin.mk #[natE, toExpr fid.obj.1, pf]
  let mapBase : Q(FromList (Std.DHashMap.getD $homsE ($i, $j) [])) ←
    mkAppOptM ``FromList.mk #[none, q((Std.DHashMap.getD $homsE ($i, $j) [])), fid']
  --let map : Q(FromList $objsE) := sorry
  let map : Expr ←
    mkAppM ``Quiver.Hom.toPath #[]
  let instCat ← g.catE
  let instCatStruct ← mkAppOptM ``Category.toCategoryStruct #[none, instCat]
  let instQuiver ← mkAppOptM ``CategoryStruct.toQuiver #[none, instCatStruct]
  let D' : Expr ← mkAppOptM ``Functor.toPrefunctor #[none, instCat, none, none, Expr.fvar fvar]
  mkAppOptM ``Prefunctor.map #[none, instQuiver, none, none, D', none, none, map]

def GraphData.diagramifiedGoal {goal : MVarId} (g : GraphData goal) (fvar : FVarId) :
    TacticM MVarId := do
  let goalType : Expr ← goal.getType
  let mut sideGoalType : Expr := goalType
  --let D : Expr ← g.functorE
  for ((i, j), l) in g.homs do
    for fId in l do
      let lhsId := g.objs.get i.obj
      let rhsId := g.objs.get j.obj
      let lhsObj ← g.functorObjE fvar i
      let rhsObj ← g.functorObjE fvar j
      let fObj ← g.functorMapE fvar i j fId
      sideGoalType := sideGoalType.replaceFVarId lhsId lhsObj
      sideGoalType := sideGoalType.replaceFVarId rhsId rhsObj
      sideGoalType := sideGoalType.replaceFVarId fId fObj
  let mvar ← mkFreshExprSyntheticOpaqueMVar sideGoalType
  let mvarId := mvar.mvarId!
  return mvarId

def GraphData.changeMVar {goal : MVarId} (g : GraphData goal) (newGoal : MVarId) :
    GraphData newGoal where
  __ := g

elab "constructDiag'" : tactic => do
  withMainContext do
  let goal ← getMainGoal
  let data ← constructGraphData goal
  let objsE : Q(List Scheme.{0}) ← data.objsE
  let J₀ : Q(Type) := q(FromList $objsE)
  --let instQuiver : Q(Quiver.{1, 0} $J₀) ← data.quiverE'
  --let D : Expr ← data.functorE'
  let D : Expr ← data.homsE'
  let (fvarD, goal) ← (← goal.define `D (← inferType D) D).intro1P
  -- add the quiver instance to the context (with definition)
  --let (_, goal) ← (← goal.define `instQuiver (← inferType instQuiver) instQuiver).intro1P
  -- change context to goal with introduced `D
  goal.withContext do
  let data := data.changeMVar goal
  --let sideGoal ← data.diagramifiedGoal fvarD
  replaceMainGoal [goal]
  --liftMetaTactic fun goal => do
    -- add `D` to the context (with definition)
    --let (_, goal) ← (← goal.define `D (← inferType D) D).intro1P
    ---- add the quiver instance to the context (with definition)
    --let (_, goal) ← (← goal.define `instQuiver (← inferType instQuiver) instQuiver).intro1P
    --let (_, sideGoal) ← (← sideGoal.define `D (← inferType D) D).intro1P
    ---- add the quiver instance to the context (with definition) let (_, sideGoal) ← (← sideGoal.define `instQuiver (← inferType instQuiver) instQuiver).intro1P
    --for fvar in data.sourceLocalisable do
      --logInfo s!"localisable on the source at: {← ppExpr (.fvar fvar)}"
      --let i : Expr := sorry
      --let tyD : Expr ← mkAppM ``Prefunctor #[J₀, q(Scheme.{0})]
      --let localiseAtFun : Expr ← withLocalDecl `D BinderInfo.default tyD fun D => do
      --  let tyU : Expr := q(Scheme.{0})
      --  withLocalDecl `U BinderInfo.implicit tyU fun U => do
      --    let X : Expr ← mkAppM ``Prefunctor.obj #[Dp, i]
      --    let tyf : Expr ← mkAppM ``Quiver.Hom #[U, X]
      --    withLocalDecl `f BinderInfo.default tyf fun f => do
      --      let locObjFun : Expr := sorry
      --      let locHomFun : Expr := sorry
      --      let Dlocp : Expr ← mkAppOptM ``Prefunctor.mk
      --        #[J₀, instQuiver, q(Scheme.{0}), none, locObjFun, locHomFun]
      --      mkAppOptM ``Paths.lift #[J₀, instQuiver, none, none, Dlocp]
      --let instLocalisor : Expr ←
      --  mkAppM ``Localisor.mk #[]
    --return [goal, sideGoal]

example {P Q : MorphismProperty Scheme.{0}} [IsLocalAtSource P] [IsLocalAtSource Q]
    {X Y : Scheme.{0}} (f : X ⟶ Y) (hf : P f) :
    Q f := by
  constructDiag'
  let x : FromList [X, Y] := ⟨⟨0, by simp⟩⟩
  let y : FromList [X, Y] := ⟨⟨1, by simp⟩⟩
  have : D x y = y := rfl
  sorry

example {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : X ⟶ Y) (u : Z ⟶ X) : True := by
  constructDiag'
  let x : Paths (FromList [X, Y, Z]) := ⟨⟨0, by simp⟩⟩
  let y : Paths (FromList [X, Y, Z]) := ⟨⟨1, by simp⟩⟩
  let z : Paths (FromList [X, Y, Z]) := ⟨⟨2, by simp⟩⟩
  have : D.obj x = X := rfl
  have : D.obj y = Y := rfl
  have : D.obj z = Z := rfl
  let hg : x ⟶ y := Quiver.Hom.toPath ⟨⟨0, by simp [x, y, Std.DHashMap.getD_insert]⟩⟩
  let hf : x ⟶ y := Quiver.Hom.toPath ⟨⟨1, by simp [x, y, Std.DHashMap.getD_insert]⟩⟩
  have : D.map hg = g := by
    dsimp only [hf]
    rw [Paths.lift_toPath]
    simp [Std.DHashMap.getD_insert, x, y]
  have : D.map hf = f := by
    dsimp only [hg]
    rw [Paths.lift_toPath]
    simp [Std.DHashMap.getD_insert, x, y]
  sorry
  sorry

end
