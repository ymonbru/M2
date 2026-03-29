import M2.Propre.KSheaf
import M2.forceColimW
import M2.Suffices
import M2.forceLimW-- a remetre au niveau par rapport à forceColimW
import Mathlib.Topology.Sheaves.Sheaf

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite TopCat

universe u v w

variable {A : Type u} [Category.{v, u} A]
variable {X : Type w} [TopologicalSpace X]

/-def baseChangeCompactNhds {K L : Compacts X} (h : K.carrier ⊆ L.carrier) : L.compactNhds → K.compactNhds := fun M => ⟨M.1, fun ⟨x,hx⟩ => M.2 ⟨x, h hx ⟩⟩

lemma monoBaseChangeCompactNhds {K L : Compacts X} (h : K.carrier ⊆ L.carrier) : Monotone <| baseChangeCompactNhds h := fun _ _ hyp => fun _ hx => hyp hx-/

noncomputable section

namespace TopCat.Presheaf

variable [HasColimitsOfSize.{w, w} A] (F : Presheaf A (of X)) {K : Compacts X}

variable (K) in
def alphaUpStarObjObj : A := colimit ((Subtype.mono_coe K.openNhds).functor.op ⋙ F)

def ιAlphaUpStarObjObj (U : (K.openNhds ) ) : F.obj (op U.val) ⟶ F.alphaUpStarObjObj K := colimit.ι ((Subtype.mono_coe K.openNhds).functor.op ⋙ F) _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma alphaUpStarObjObj_w {U V : (K.openNhds)} (i : op U ⟶ op V) : F.map i ≫ F.ιAlphaUpStarObjObj V = F.ιAlphaUpStarObjObj U := colimit.w ((Subtype.mono_coe K.openNhds).functor.op ⋙ F) i

variable (K) in
@[simps]
def alphaUpStarObjObjCocone : Cocone ((Subtype.mono_coe K.openNhds).functor.op ⋙ F) where
 pt := alphaUpStarObjObj F K
 ι.app U := ιAlphaUpStarObjObj F U.unop

variable (K) in
def isColimitAlphaUpStarObjObjCocone : IsColimit (alphaUpStarObjObjCocone F K) := colimit.isColimit _

def ιAlphaUpStarObjObjRc (U : (K.openRcNhds ) ) : F.obj (op U.val) ⟶ F.alphaUpStarObjObj K := F.ιAlphaUpStarObjObj (K.mono_oRcNhds_to_openNhds.functor.obj U)

variable (K) in
@[simps]
def alphaUpStarObjObjRcCocone : Cocone ((Subtype.mono_coe K.openRcNhds).functor.op ⋙ F) where
  pt := alphaUpStarObjObj F K
  ι.app U := ιAlphaUpStarObjObjRc F U.unop
  ι.naturality U V f:= by
    dsimp
    simpa only [Category.comp_id] using alphaUpStarObjObj_w F (K.mono_oRcNhds_to_openNhds.functor.map f.unop).op

variable (K) in
def isColimitAlphaUpStarObjObjRcCocone [T2Space X] [LocallyCompactSpace X] : IsColimit (alphaUpStarObjObjRcCocone F K) := (Functor.Final.isColimitWhiskerEquiv (K.mono_oRcNhds_to_openNhds.functor.op) _).2
  (isColimitAlphaUpStarObjObjCocone _ _)

variable {F} in
@[ext]
lemma alphaUpStarObjObj_hom_ext {Y : A} (f g : F.alphaUpStarObjObj K ⟶ Y) (h : ∀ U : K.openNhds, F.ιAlphaUpStarObjObj U ≫ f = F.ιAlphaUpStarObjObj U ≫ g) : f = g := (isColimitAlphaUpStarObjObjCocone F K).hom_ext (fun _ ↦ h _)

variable {F} in
@[ext]
lemma alphaUpStarObjObjRC_hom_ext [T2Space X] [LocallyCompactSpace X] {Y : A} (f g : F.alphaUpStarObjObj K ⟶ Y) (h : ∀ U : K.openRcNhds, F.ιAlphaUpStarObjObjRc U ≫ f = F.ιAlphaUpStarObjObjRc U ≫ g) : f = g := (isColimitAlphaUpStarObjObjRcCocone F K).hom_ext (fun _ ↦ h _)

def alphaUpStarObjObj_desc (c : Cocone <| (Subtype.mono_coe K.openNhds).functor.op ⋙ F) : F.alphaUpStarObjObj K ⟶ c.pt := colimit.desc _ c

@[reassoc (attr := simp)]
lemma alphaUpStarObjObj_ι_desc {K : Compacts X} (c : Cocone <| (Subtype.mono_coe K.openNhds).functor.op ⋙ F) (U : K.openNhds ) : F.ιAlphaUpStarObjObj U ≫ (isColimitAlphaUpStarObjObjCocone F K).desc c = c.ι.app (op U) := colimit.ι_desc c (op U)

def alphaUpStarObjMap {K L : Compacts X} (i : K ⟶ L) : F.alphaUpStarObjObj L ⟶ F.alphaUpStarObjObj K := colimit.pre ((Subtype.mono_coe K.openNhds).functor.op ⋙ F) (monoBaseChangeOpenNhds i).functor.op

@[reassoc (attr := simp)]
lemma ι_alphaUpStarObjMap {K L : Compacts X} (i : K ⟶ L) (U : L.openNhds ) : F.ιAlphaUpStarObjObj U ≫ F.alphaUpStarObjMap i = F.ιAlphaUpStarObjObj ( (monoBaseChangeOpenNhds i).functor.obj U) := colimit.ι_pre ((Subtype.mono_coe K.openNhds).functor.op ⋙ F) (monoBaseChangeOpenNhds i).functor.op _

set_option backward.isDefEq.respectTransparency false in
@[simps]
def alphaUpStarObj (F : Presheaf A (of X)) : (Compacts X)ᵒᵖ ⥤ A where
  obj K := F.alphaUpStarObjObj (K.unop)
  map i := F.alphaUpStarObjMap i.unop

def alphaUpStarMapApp { F1 F2 : Presheaf A (of X)} (τ : F1 ⟶ F2) (K : Compacts X): F1.alphaUpStarObjObj K ⟶ F2.alphaUpStarObjObj K := colimMap <| Functor.whiskerLeft _ τ

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma ι_alphaUpStarMapApp { F1 F2 : Presheaf A (of X)} (τ : F1 ⟶ F2) {K : Compacts X} (U : K.openNhds) : F1.ιAlphaUpStarObjObj U ≫ alphaUpStarMapApp τ K = τ.app (op U.val) ≫ F2.ιAlphaUpStarObjObj U := Limits.ι_colimMap _ _

attribute [local simp] Quiver.Hom.baseChangeOpenNhds in
@[simps]
def alphaUpStarMap {F1 F2 : Presheaf A (of X)} (τ : F1 ⟶ F2) : F1.alphaUpStarObj ⟶ F2.alphaUpStarObj where
  app K := alphaUpStarMapApp τ K.unop

-- a envoyer dans l'api de `TopCat.Presheaf` du coup
@[simp] theorem id_app {C : Type*} [Category* C] {X : TopCat} (P : Presheaf C X) (U : (Opens X)ᵒᵖ) : NatTrans.app (𝟙 P) U = 𝟙 _ := rfl

@[simps]
def alphaUpStar : Presheaf A (of X) ⥤ KPresheaf A X where
  obj := alphaUpStarObj
  map := alphaUpStarMap

end TopCat.Presheaf

namespace TopCat.KPresheaf

variable [HasLimitsOfSize.{w, w} A] (G : KPresheaf A (of X)) {U : Opens X}

variable (U) in
def alphaDownStarObjObj (U : Opens X) : A := limit ((Subtype.mono_coe U.compactInsd).functor.op ⋙ G)

def πAlphaDownStarObjObj (K : U.compactInsd) : G.alphaDownStarObjObj U ⟶ G.obj (op K.val) := limit.π ((Subtype.mono_coe U.compactInsd).functor.op ⋙ G) _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma alphaDownStarObjObj_w {K L : U.compactInsd} (i : op K ⟶ op L) : G.πAlphaDownStarObjObj K ≫ G.map i = G.πAlphaDownStarObjObj L := limit.w _ i

variable (U) in
@[simps]
def alphaDownStarObjObjCone : Cone ((Subtype.mono_coe U.compactInsd).functor.op ⋙ G) where
  pt := alphaDownStarObjObj G U
  π.app U := πAlphaDownStarObjObj G U.unop

variable (U) in
def isLimitAlphaDownStarObjObjCone : IsLimit (alphaDownStarObjObjCone G U) := limit.isLimit _

@[ext]
lemma alphaDownStarObjObj_hom_ext {Y : A} (f g : Y ⟶ G.alphaDownStarObjObj U) (h : ∀ K : U.compactInsd, f ≫ G.πAlphaDownStarObjObj K = g ≫ G.πAlphaDownStarObjObj K ) : f = g := (G.isLimitAlphaDownStarObjObjCone _ ).hom_ext (fun _ ↦ h _)

def alphaDownStarObjMap {U V : Opens X} (i : U ⟶ V) : G.alphaDownStarObjObj V ⟶ G.alphaDownStarObjObj U := limit.pre ((Subtype.mono_coe V.compactInsd).functor.op ⋙ G) (monoBaseChangeCompactInsd i).functor.op

@[reassoc (attr := simp)]
lemma alphaDownStarObjMap_π {U V : Opens X} (i : U ⟶ V) (K : U.compactInsd) : G.alphaDownStarObjMap i ≫ G.πAlphaDownStarObjObj K = G.πAlphaDownStarObjObj ( (monoBaseChangeCompactInsd i).functor.obj K) := limit.pre_π _ (monoBaseChangeCompactInsd i).functor.op (op K)

@[reassoc (attr := simp)]
lemma alphaDownStarObjObj_lift_π {U : Opens X} (c : Cone <| (Subtype.mono_coe U.compactInsd).functor.op ⋙ G) (K : U.compactInsd): (G.isLimitAlphaDownStarObjObjCone _ ).lift c ≫ G.πAlphaDownStarObjObj K = c.π.app (op K) := limit.lift_π c (op K)

set_option backward.isDefEq.respectTransparency false in
@[simps]
def alphaDownStarObj (G : KPresheaf A (of X)) : (Opens X)ᵒᵖ ⥤ A where
 obj U := G.alphaDownStarObjObj U.unop
 map i := G.alphaDownStarObjMap i.unop


def alphaDownStarMapApp { G1 G2 : KPresheaf A (of X)} (σ : G1 ⟶ G2) (U : Opens X): G1.alphaDownStarObjObj U ⟶ G2.alphaDownStarObjObj U := limMap <| Functor.whiskerLeft _ σ

@[reassoc (attr := simp)]
lemma alphaDownStarMapApp_π { G1 G2 : KPresheaf A (of X)} (σ : G1 ⟶ G2) {U : Opens X} (K : U.compactInsd) : alphaDownStarMapApp σ U ≫ G2.πAlphaDownStarObjObj K = G1.πAlphaDownStarObjObj K ≫ σ.app (op K.val) := limMap_π _ (op K)

set_option backward.isDefEq.respectTransparency false in
@[simps]
def alphaDownStarMap {G1 G2 : KPresheaf A (of X)} (σ : G1 ⟶ G2) : G1.alphaDownStarObj ⟶ G2.alphaDownStarObj where
app U := alphaDownStarMapApp σ U.unop

@[simp] theorem id_app {C : Type*} [Category* C] (P : KPresheaf C X) (K : (Compacts X)ᵒᵖ) :
    NatTrans.app (𝟙 P) K = 𝟙 _ := rfl


set_option backward.isDefEq.respectTransparency false in
@[simps]
def alphaDownStar : KPresheaf A X ⥤ Presheaf A (of X) where
 obj := alphaDownStarObj
 map := alphaDownStarMap
 map_id G := by
  apply NatTrans.ext
  ext : 2
  simp_all only [alphaDownStarObj_obj, alphaDownStarMap_app,TopCat.Presheaf, NatTrans.id_app]--aesop ne trouve pas TopCat.Presheaf
  -- TopCat.Presheaf n'est pas pareil que TopCat.KPresheaf
  ext : 1
  simp_all only [alphaDownStarMapApp_π, id_app, Category.id_comp, Category.comp_id]
 map_comp _ _ := by
  apply NatTrans.ext
  ext
  apply alphaDownStarObjObj_hom_ext
  intro
  rw [ NatTrans.comp_app]
  simp

end TopCat.KPresheaf

namespace CategoryTheory.NatTrans

variable [HasColimitsOfSize.{w, w} A] [HasLimitsOfSize.{w, w} A]

open TopCat.KPresheaf TopCat.Presheaf
variable {F : Presheaf A (of X)} {G : KPresheaf A X} (τ : (alphaUpStar).obj F ⟶ G) (σ : F ⟶ (alphaDownStar).obj G) (K : Compacts X) (U : Opens X)

set_option backward.isDefEq.respectTransparency false in
@[simps]
def toFtoαGCone : Cone <| (Subtype.mono_coe U.compactInsd).functor.op ⋙ G where--:= Cone.mk _ (τ.toFtoαGConeπ _ )
  pt := F.obj (op U)
  π.app K := F.ιAlphaUpStarObjObj ( K.unop.toOpenNhds) ≫ τ.app (op K.unop.val)
  π.naturality {K L} i:= by
    simp [← τ.naturality]
    rfl

set_option backward.isDefEq.respectTransparency false in
@[simps]
def toFtoαG : F ⟶ alphaDownStar.obj G where
 app U := (G.isLimitAlphaDownStarObjObjCone _ ).lift (τ.toFtoαGCone U.unop)
 naturality {U V} i := by
  apply alphaDownStarObjObj_hom_ext
  intro K
  simp [Quiver.Hom.baseChangeCompactInsd, ιAlphaUpStarObjObj]
  forceColimW

set_option backward.isDefEq.respectTransparency false in
@[simps]
def toαFtoGCocone : Cocone <| (Subtype.mono_coe K.openNhds).functor.op ⋙ F where
  pt := G.obj (op K)
  ι.app U := σ.app _ ≫ G.πAlphaDownStarObjObj (U.unop.toCompactInsd)

set_option backward.isDefEq.respectTransparency false in
@[simps]
def toαFtoG : alphaUpStar.obj F ⟶ G where
 app K := (F.isColimitAlphaUpStarObjObjCocone _ ).desc (σ.toαFtoGCocone _)
 naturality {K L} i := by
  apply alphaUpStarObjObj_hom_ext
  intro
  simp [πAlphaDownStarObjObj]
  forceLimW

end NatTrans

--namespace TopCat.KPresheaf-- ça fait des trucs bizzares avec homEquiv

open TopCat.Presheaf TopCat.KPresheaf

variable [HasColimitsOfSize.{w, w, v, u} A] [HasLimitsOfSize.{w, w, v, u} A] (F : Presheaf A (of X)) (G : KPresheaf A X)

set_option backward.isDefEq.respectTransparency false in
/-- The bijection between hom(αF, G) and hom(F,αG) -/
def homEquivAlpha: (alphaUpStar.obj F ⟶ G) ≃ ( F ⟶ alphaDownStar.obj G) where
 toFun := fun τ => τ.toFtoαG
 invFun := fun σ => σ.toαFtoG
 left_inv _ := by aesop_cat
 right_inv _ := by aesop_cat

set_option backward.isDefEq.respectTransparency false in
/-- The data necessary to build the adjunction between α^* and α_*-/
def adjAlphaThm : Adjunction.CoreHomEquiv (alphaUpStar (A := A) (X := X)) alphaDownStar where
homEquiv := homEquivAlpha
homEquiv_naturality_left_symm _ _ := by
  ext
  apply alphaUpStarObjObj_hom_ext
  intro
  simp [homEquivAlpha]
homEquiv_naturality_right {F G1 G2} τ σ := by
  ext
  apply alphaDownStarObjObj_hom_ext
  intro
  simp [homEquivAlpha]

/-- The adjunction between α^* and α_*-/
def AdjAlpha : (alphaUpStar (A := A) (X := X)) ⊣ (alphaDownStar ) := Adjunction.mkOfHomEquiv (adjAlphaThm)
