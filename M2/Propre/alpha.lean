import M2.Propre.KSheaf
import Mathlib.Topology.Sheaves.Presheaf

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite TopCat Opens

universe u v w

variable {A : Type u} [Category.{v, u} A]
variable {X : TopCat.{w}}

noncomputable section

namespace TopCat.Presheaf

variable [HasColimitsOfSize.{w, w} A] (F : Presheaf A X) {K : Compacts X}

variable (K) in
/--The `.obj` component of `TopCat.Presheaf.toKPresheafFunctorObj`.-/
def toKPresheafFunctorObjObj : A := colimit ((Subtype.mono_coe K.openNhds).functor.op ⋙ F)

/-- The canonical map from a value of the presheaf over an open subset to a value of it's coresponding Kpresheaf.-/
def ιToKPresheafFunctorObjObj (U : (K.openNhds)) : F.obj (op U.val) ⟶ F.toKPresheafFunctorObjObj K := colimit.ι ((Subtype.mono_coe K.openNhds).functor.op ⋙ F) _

@[reassoc (attr := simp)]
lemma toKPresheafFunctorObjObj_w {U V : (K.openNhds)} (i : op U ⟶ op V) : F.map i ≫ F.ιToKPresheafFunctorObjObj V = F.ιToKPresheafFunctorObjObj U := colimit.w ((Subtype.mono_coe K.openNhds).functor.op ⋙ F) i

variable (K) in
/-- The cocone structure of `F.toKPresheafFunctorObjObj K` over all values of opens subset that contains `K`.-/
@[simps]
def toKPresheafFunctorObjObjCocone : Cocone ((Subtype.mono_coe K.openNhds).functor.op ⋙ F) where
 pt := F.toKPresheafFunctorObjObj K
 ι.app U := ιToKPresheafFunctorObjObj F U.unop

variable (K) in
/-- The evidence that `F.toKPresheafFunctorObjObjCocone` is a colimit cocone.-/
def isColimitToKPresheafFunctorObjObjCocone : IsColimit (toKPresheafFunctorObjObjCocone F K) := colimit.isColimit _

variable {F} in
@[ext]
lemma toKPresheafFunctorObjObj_hom_ext {Y : A} (f g : F.toKPresheafFunctorObjObj K ⟶ Y) (h : ∀ U : K.openNhds, F.ιToKPresheafFunctorObjObj U ≫ f = F.ιToKPresheafFunctorObjObj U ≫ g) : f = g := (F.isColimitToKPresheafFunctorObjObjCocone K).hom_ext (fun _ ↦ h _)

@[reassoc (attr := simp)]
lemma toKPresheafFunctorObjObj_ι_desc {K : Compacts X} (c : Cocone <| (Subtype.mono_coe K.openNhds).functor.op ⋙ F) (U : K.openNhds ) : F.ιToKPresheafFunctorObjObj U ≫ (isColimitToKPresheafFunctorObjObjCocone F K).desc c = c.ι.app (op U) := colimit.ι_desc c (op U)

/-- The canonical map from a value of the presheaf over an open subset relatively compact to a value of it's coresponding Kpresheaf.-/
def ιToKPresheafFunctorObjObjRc (U : (K.openRcNhds)) : F.obj (op U.val) ⟶ F.toKPresheafFunctorObjObj K := F.ιToKPresheafFunctorObjObj (K.mono_oRcNhds_to_openNhds.functor.obj U)

variable (K) in
/-- The cocone structure of `F.toKPresheafFunctorObjObj K` over all values of opens subset relatively compact that contains `K`.-/
@[simps]
def toKPresheafFunctorObjObjRcCocone : Cocone ((Subtype.mono_coe K.openRcNhds).functor.op ⋙ F) where
  pt := toKPresheafFunctorObjObj F K
  ι.app U := ιToKPresheafFunctorObjObjRc F U.unop
  ι.naturality U V f:= by
    dsimp
    simpa only [Category.comp_id] using toKPresheafFunctorObjObj_w F (K.mono_oRcNhds_to_openNhds.functor.map f.unop).op

variable (K) in
/-- The evidence that `F.toKPresheafFunctorObjObjRcCocone` is a colimit cocone.-/
def isColimitToKPresheafFunctorObjObjRcCocone [T2Space X] [LocallyCompactSpace X] : IsColimit (toKPresheafFunctorObjObjRcCocone F K) := (Functor.Final.isColimitWhiskerEquiv (K.mono_oRcNhds_to_openNhds.functor.op) _).2
  (isColimitToKPresheafFunctorObjObjCocone _ _)

variable {F} in
@[ext]
lemma toKPresheafFunctorObjObjRC_hom_ext [T2Space X] [LocallyCompactSpace X] {Y : A} (f g : F.toKPresheafFunctorObjObj K ⟶ Y) (h : ∀ U : K.openRcNhds, F.ιToKPresheafFunctorObjObjRc U ≫ f = F.ιToKPresheafFunctorObjObjRc U ≫ g) : f = g := (isColimitToKPresheafFunctorObjObjRcCocone F K).hom_ext (fun _ ↦ h _)

@[reassoc (attr := simp)]
lemma toKPresheafFunctorObjObjRc_ι_desc [T2Space X] [LocallyCompactSpace X] {K : Compacts X} (c : Cocone <| (Subtype.mono_coe K.openRcNhds).functor.op ⋙ F) (U : K.openRcNhds ) : F.ιToKPresheafFunctorObjObjRc U ≫ (isColimitToKPresheafFunctorObjObjRcCocone F K).desc c = c.ι.app (op U) := (isColimitToKPresheafFunctorObjObjRcCocone F K).fac _ _

/-- The `.map` component of `TopCat.Presheaf.toKPresheafFunctorObj`-/
def toKPresheafFunctorObjMap {K L : Compacts X} (i : K ⟶ L) : F.toKPresheafFunctorObjObj L ⟶ F.toKPresheafFunctorObjObj K := colimit.pre ((Subtype.mono_coe K.openNhds).functor.op ⋙ F) (monoBaseChangeOpenNhds i).functor.op

@[reassoc (attr := simp)]
lemma ι_toKPresheafFunctorObjMap {K L : Compacts X} (i : K ⟶ L) (U : L.openNhds ) : F.ιToKPresheafFunctorObjObj U ≫ F.toKPresheafFunctorObjMap i = F.ιToKPresheafFunctorObjObj ( (monoBaseChangeOpenNhds i).functor.obj U) := colimit.ι_pre ((Subtype.mono_coe K.openNhds).functor.op ⋙ F) (monoBaseChangeOpenNhds i).functor.op _

set_option backward.isDefEq.respectTransparency false in
/-- The Kpresheaf associated to a presheaf.-/
@[simps]
def toKPresheafFunctorObj (F : Presheaf A X) : KPresheaf A X where
  obj K := F.toKPresheafFunctorObjObj (K.unop)
  map i := F.toKPresheafFunctorObjMap i.unop

/-- The `.app` component of `TopCat.Presheaf.toKPresheafFunctorMap`.-/
def toKPresheafFunctorMapApp { F1 F2 : Presheaf A X} (τ : F1 ⟶ F2) (K : Compacts X): F1.toKPresheafFunctorObjObj K ⟶ F2.toKPresheafFunctorObjObj K := colimMap <| Functor.whiskerLeft _ τ

@[reassoc (attr := simp)]
lemma ι_toKPresheafFunctorMapApp { F1 F2 : Presheaf A X} (τ : F1 ⟶ F2) {K : Compacts X} (U : K.openNhds) : F1.ιToKPresheafFunctorObjObj U ≫ toKPresheafFunctorMapApp τ K = τ.app (op U.val) ≫ F2.ιToKPresheafFunctorObjObj U := Limits.ι_colimMap _ _

attribute [local simp] baseChangeOpenNhds in
/-- The natural transformation between Kpresheaves induced by a natural transformation between their coresponding presheaves.-/
@[simps]
def toKPresheafFunctorMap {F1 F2 : Presheaf A X} (τ : F1 ⟶ F2) : F1.toKPresheafFunctorObj ⟶ F2.toKPresheafFunctorObj where
  app K := toKPresheafFunctorMapApp τ K.unop

-- a envoyer dans l'api de `TopCat.Presheaf` du coup
@[simp] theorem id_app {C : Type*} [Category* C] {X : TopCat} (P : Presheaf C X) (U : (Opens X)ᵒᵖ) : NatTrans.app (𝟙 P) U = 𝟙 _ := rfl

/-- The functor sending Presheaves into Kpresheaves.-/
@[simps]
def toKPresheafFunctor : Presheaf A X ⥤ KPresheaf A X where
  obj := toKPresheafFunctorObj
  map := toKPresheafFunctorMap

end TopCat.Presheaf

namespace TopCat.KPresheaf

variable [HasLimitsOfSize.{w, w} A] (G : KPresheaf A X) {U : Opens X}

variable (U) in
/--The `.obj` component of `TopCat.KPresheaf.toPresheafFunctorObj`.-/
def toPresheafFunctorObjObj (U : Opens X) : A := limit ((Subtype.mono_coe U.compactInsd).functor.op ⋙ G)

/-- The canonical map to a value of the Kpresheaf over a compact subset to a value of it's coresponding Presheaf.-/
def πToPresheafFunctorObjObj (K : U.compactInsd) : G.toPresheafFunctorObjObj U ⟶ G.obj (op K.val) := limit.π ((Subtype.mono_coe U.compactInsd).functor.op ⋙ G) _

@[reassoc (attr := simp)]
lemma toPresheafFunctorObjObj_w {K L : U.compactInsd} (i : op K ⟶ op L) : G.πToPresheafFunctorObjObj K ≫ G.map i = G.πToPresheafFunctorObjObj L := limit.w _ i

variable (U) in
/-- The cone structure of `G.toPresheafFunctorObjObj U` over all values of compacts subset inside `U`.-/
@[simps]
def toPresheafFunctorObjObjCone : Cone ((Subtype.mono_coe U.compactInsd).functor.op ⋙ G) where
  pt := G.toPresheafFunctorObjObj U
  π.app U := πToPresheafFunctorObjObj G U.unop

variable (U) in
/-- The evidence that `G.toPresheafFunctorObjObjCone` is a limit cone. -/
def isLimitToPresheafFunctorObjObjCone : IsLimit (toPresheafFunctorObjObjCone G U) := limit.isLimit _

@[ext]
lemma toPresheafFunctorObjObj_hom_ext {Y : A} (f g : Y ⟶ G.toPresheafFunctorObjObj U) (h : ∀ K : U.compactInsd, f ≫ G.πToPresheafFunctorObjObj K = g ≫ G.πToPresheafFunctorObjObj K ) : f = g := (G.isLimitToPresheafFunctorObjObjCone _ ).hom_ext (fun _ ↦ h _)

@[reassoc (attr := simp)]
lemma toPresheafFunctorObjObj_lift_π {U : Opens X} (c : Cone <| (Subtype.mono_coe U.compactInsd).functor.op ⋙ G) (K : U.compactInsd): (G.isLimitToPresheafFunctorObjObjCone _ ).lift c ≫ G.πToPresheafFunctorObjObj K = c.π.app (op K) := limit.lift_π c (op K)

/-- The `.map` component of `TopCat.KPresheaf.toPresheafFunctorObj`.-/
def toPresheafFunctorObjMap {U V : Opens X} (i : U ⟶ V) : G.toPresheafFunctorObjObj V ⟶ G.toPresheafFunctorObjObj U := limit.pre ((Subtype.mono_coe V.compactInsd).functor.op ⋙ G) (monoBaseChangeCompactInsd i).functor.op

@[reassoc (attr := simp)]
lemma toPresheafFunctorObjMap_π {U V : Opens X} (i : U ⟶ V) (K : U.compactInsd) : G.toPresheafFunctorObjMap i ≫ G.πToPresheafFunctorObjObj K = G.πToPresheafFunctorObjObj ( (monoBaseChangeCompactInsd i).functor.obj K) := limit.pre_π _ (monoBaseChangeCompactInsd i).functor.op (op K)

set_option backward.isDefEq.respectTransparency false in
/-- The presheaf associated to a Kpresheaf.-/
@[simps]
def toPresheafFunctorObj (G : KPresheaf A (of X)) : Presheaf A (of X) where
 obj U := G.toPresheafFunctorObjObj U.unop
 map i := G.toPresheafFunctorObjMap i.unop

/-- The `.app` component of `TopCat.KPresheaf.toPresheafFunctorMap`.-/
def toPresheafFunctorMapApp { G1 G2 : KPresheaf A (of X)} (σ : G1 ⟶ G2) (U : Opens X): G1.toPresheafFunctorObjObj U ⟶ G2.toPresheafFunctorObjObj U := limMap <| Functor.whiskerLeft _ σ

@[reassoc (attr := simp)]
lemma toPresheafFunctorMapApp_π { G1 G2 : KPresheaf A (of X)} (σ : G1 ⟶ G2) {U : Opens X} (K : U.compactInsd) : toPresheafFunctorMapApp σ U ≫ G2.πToPresheafFunctorObjObj K = G1.πToPresheafFunctorObjObj K ≫ σ.app (op K.val) := limMap_π _ (op K)

set_option backward.isDefEq.respectTransparency false in
/-- The natural transformation between presheaves induced by a natural transformation between their coresponding Kpresheaves.-/
@[simps]
def toPresheafFunctorMap {G1 G2 : KPresheaf A X} (σ : G1 ⟶ G2) : G1.toPresheafFunctorObj ⟶ G2.toPresheafFunctorObj where
app U := toPresheafFunctorMapApp σ U.unop

/-- The functor sending Kpresheaves into presheaves.-/
@[simps]
def toPresheafFunctor : KPresheaf A (of X) ⥤ Presheaf A (of X) where
  obj := toPresheafFunctorObj
  map := toPresheafFunctorMap

end TopCat.KPresheaf

namespace TopCat.KPresheaf.adjunction

variable [HasColimitsOfSize.{w, w} A] [HasLimitsOfSize.{w, w} A]

open TopCat.Presheaf
variable {F : Presheaf A (of X)} {G : KPresheaf A X} (τ : (toKPresheafFunctor).obj F ⟶ G) (σ : F ⟶ (toPresheafFunctor).obj G) (K : Compacts X) (U : Opens X)

set_option backward.isDefEq.respectTransparency false in
@[simps]
def homEquivToFunCone : Cone <| (Subtype.mono_coe U.compactInsd).functor.op ⋙ G where
  pt := F.obj (op U)
  π.app K := F.ιToKPresheafFunctorObjObj ( toOpenNhds K.unop) ≫ τ.app (op K.unop.val)
  π.naturality {K L} i:= by
    simp [← τ.naturality]
    rfl

set_option backward.isDefEq.respectTransparency false in
@[simps]
def homEquivToFun : F ⟶ toPresheafFunctor.obj G where
 app U := (G.isLimitToPresheafFunctorObjObjCone U.unop).lift (homEquivToFunCone τ U.unop)
 naturality {U V} i := by
  apply toPresheafFunctorObjObj_hom_ext
  intro K
  simpa [baseChangeCompactInsd] using toKPresheafFunctorObjObj_w_assoc _ (show op (toOpenNhds (baseChangeCompactInsd i.unop K)) ⟶ op (toOpenNhds K) from i) _

set_option backward.isDefEq.respectTransparency false in
@[simps]
def homEquivInvFunCocone : Cocone <| (Subtype.mono_coe K.openNhds).functor.op ⋙ F where
  pt := G.obj (op K)
  ι.app U := σ.app _ ≫ G.πToPresheafFunctorObjObj (toCompactInsd U.unop)

set_option backward.isDefEq.respectTransparency false in
@[simps]
def homEquivInvFun : toKPresheafFunctor.obj F ⟶ G where
 app K := (F.isColimitToKPresheafFunctorObjObjCocone K.unop).desc (homEquivInvFunCocone σ _)
 naturality {K L} i := by
  apply toKPresheafFunctorObjObj_hom_ext
  intro U
  simpa [baseChangeOpenNhds] using whisker_eq _ (toPresheafFunctorObjObj_w G  (show op (toCompactInsd U) ⟶ op (toCompactInsd (baseChangeOpenNhds i.unop U)) from i)).symm

variable (F) in
set_option backward.isDefEq.respectTransparency false in
/-- The bijection between hom(F.toKPresheafFunctorObj, G) and hom(F,G.toPresheafFunctorObj) -/
def homEquiv: (toKPresheafFunctor.obj F ⟶ G) ≃ (F ⟶ toPresheafFunctor.obj G) where
 toFun := homEquivToFun
 invFun := fun σ => homEquivInvFun σ
 left_inv _ := by aesop
 right_inv _ := by aesop

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] homEquiv in
/-- The data necessary to build the adjunction between `toKPresheafFunctor` and `toPresheafFunctor`-/
def coreHomEquiv : Adjunction.CoreHomEquiv (toKPresheafFunctor (A := A) (X := X)) toPresheafFunctor where
homEquiv := adjunction.homEquiv

/-- The adjunction between α^* and α_*-/
def Adjunction : (toKPresheafFunctor (A := A) (X := X)) ⊣ (toPresheafFunctor ) := Adjunction.mkOfHomEquiv coreHomEquiv

end TopCat.KPresheaf.adjunction

#min_imports
