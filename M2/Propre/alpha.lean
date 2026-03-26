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

variable [HasColimitsOfSize.{w, w} A] (F : Presheaf A (of X)) {K : (Compacts X)ᵒᵖ}

def alphaUpStarObjObj (K : (Compacts X)ᵒᵖ ) : A := colimit ((Subtype.mono_coe K.unop.openNhds).functor.op ⋙ F)

def alphaUpStarObjObj_ι (U : (K.unop.openNhds )ᵒᵖ ) : F.obj (op U.unop.val)  ⟶ F.alphaUpStarObjObj K := colimit.ι ((Subtype.mono_coe K.unop.openNhds).functor.op ⋙ F) _


--cette version ne ser à rien
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma alphaUpStarObjObj_w {U V : (K.unop.openNhds)ᵒᵖ} (i : U ⟶ V) : F.map i ≫ F.alphaUpStarObjObj_ι V = F.alphaUpStarObjObj_ι U := by
  unfold alphaUpStarObjObj_ι
  forceColimW

@[simp]
lemma alphaUpStarObjObj_w_assoc {U V : (K.unop.openNhds)ᵒᵖ} (i : U ⟶ V) {Z : A} (h : _ ⟶ Z ): F.map i ≫ F.alphaUpStarObjObj_ι V ≫ h = F.alphaUpStarObjObj_ι U ≫ h := by
  rw [← Category.assoc, alphaUpStarObjObj_w]

@[ext]
lemma alphaUpStarObjObj_hom_ext {Y : A} (f g : F.alphaUpStarObjObj K ⟶ Y) : (∀ U : (K.unop.openNhds)ᵒᵖ, F.alphaUpStarObjObj_ι U ≫ f = F.alphaUpStarObjObj_ι U ≫ g) → f = g := colimit.hom_ext

def alphaUpStarObjObj_desc {K : (Compacts X)ᵒᵖ} (c : Cocone <| (Subtype.mono_coe K.unop.openNhds).functor.op ⋙ F) : F.alphaUpStarObjObj K ⟶ c.pt := colimit.desc _ c

@[simp]
lemma alphaUpStarObjObj_ι_desc {K : (Compacts X)ᵒᵖ} (c : Cocone <| (Subtype.mono_coe K.unop.openNhds).functor.op ⋙ F) (U : (K.unop.openNhds)ᵒᵖ ) : F.alphaUpStarObjObj_ι U ≫ F.alphaUpStarObjObj_desc c = c.ι.app U := colimit.ι_desc c U

@[simp]
lemma alphaUpStarObjObj_ι_desc_assoc {K : (Compacts X)ᵒᵖ} (c : Cocone <| (Subtype.mono_coe K.unop.openNhds).functor.op ⋙ F) (U : (K.unop.openNhds)ᵒᵖ ) {Z : A} (h : _ ⟶ Z) : F.alphaUpStarObjObj_ι U ≫ F.alphaUpStarObjObj_desc c ≫ h = c.ι.app U ≫ h:= colimit.ι_desc_assoc c U _

def alphaUpStarObjObjRc_ι (U : (K.unop.openRcNhds )ᵒᵖ ) : F.obj (op U.unop.val)  ⟶ F.alphaUpStarObjObj K := colimit.ι ((Subtype.mono_coe K.unop.openRcNhds).functor.op ⋙ F) _ ≫ colimit.pre ((Subtype.mono_coe K.unop.openNhds).functor.op ⋙ F) (K.unop.mono_oRcNhds_to_openNhds.functor.op)

@[simp]
lemma alphaUpStarObObj_Rc_ι_Eq_ι (U : (K.unop.openRcNhds )ᵒᵖ ) : F.alphaUpStarObjObjRc_ι U = F.alphaUpStarObjObj_ι (K.unop.mono_oRcNhds_to_openNhds.functor.op.obj U) := by
  unfold alphaUpStarObjObjRc_ι alphaUpStarObjObj_ι
  rw [← colimit.ι_pre]
  rfl

@[ext]
lemma alphaUpStarObjObjRc_hom_ext [T2Space X] [LocallyCompactSpace X] {Y : A} (f g : F.alphaUpStarObjObj K ⟶ Y) : (∀ U : (K.unop.openRcNhds)ᵒᵖ, F.alphaUpStarObjObjRc_ι U ≫ f = F.alphaUpStarObjObjRc_ι U ≫ g) → f = g := by
  intro h
  apply ((Functor.Final.isColimitWhiskerEquiv ((K.unop.mono_oRcNhds_to_openNhds.functor.op)) _).invFun  (colimit.isColimit _)).hom_ext
  intro U
  let h := h U
  rw [alphaUpStarObObj_Rc_ι_Eq_ι] at h
  exact h

def alphaUpStarObjObjRc_desc [T2Space X] [LocallyCompactSpace X] {K : (Compacts X)ᵒᵖ} (c : Cocone <| (Subtype.mono_coe K.unop.openRcNhds).functor.op ⋙ F) : F.alphaUpStarObjObj K ⟶ c.pt := ((Functor.Final.isColimitWhiskerEquiv ((K.unop.mono_oRcNhds_to_openNhds.functor.op)) _).invFun  (colimit.isColimit _)).desc _

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma alphaUpStarObjObjRc_ι_desc [T2Space X] [LocallyCompactSpace X] {K : (Compacts X)ᵒᵖ} (c : Cocone <| (Subtype.mono_coe K.unop.openRcNhds).functor.op ⋙ F) (U : (K.unop.openRcNhds)ᵒᵖ ) : F.alphaUpStarObjObjRc_ι U ≫ F.alphaUpStarObjObjRc_desc c = c.ι.app U := by
  rw [← ((Functor.Final.isColimitWhiskerEquiv ((K.unop.mono_oRcNhds_to_openNhds.functor.op)) _).invFun  (colimit.isColimit ((Subtype.mono_coe K.unop.openNhds).functor.op ⋙ F))).fac c U]
  simp
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma alphaUpStarObjObjRc_desc_Rc_Eq_desc [T2Space X] [LocallyCompactSpace X] {K : (Compacts X)ᵒᵖ} (c : Cocone <| (Subtype.mono_coe K.unop.openNhds).functor.op ⋙ F) : F.alphaUpStarObjObj_desc c = F.alphaUpStarObjObjRc_desc (Cocone.whisker (K.unop.mono_oRcNhds_to_openNhds.functor.op) c) := by
  ext
  rw [alphaUpStarObjObjRc_ι_desc]
  simp

@[simp]
lemma alphaUpStarObjObjRc_ι_desc_assoc [T2Space X] [LocallyCompactSpace X] {K : (Compacts X)ᵒᵖ} (c : Cocone <| (Subtype.mono_coe K.unop.openRcNhds).functor.op ⋙ F) (U : (K.unop.openRcNhds)ᵒᵖ ) {Z : A} (h : _ ⟶ Z) : F.alphaUpStarObjObjRc_ι U ≫ F.alphaUpStarObjObjRc_desc c ≫ h = c.ι.app U ≫ h:= by
  rw [← Category.assoc, alphaUpStarObjObjRc_ι_desc]
  rfl


def alphaUpStarObjMap {K L : (Compacts X)ᵒᵖ} (i : K ⟶ L) : F.alphaUpStarObjObj K ⟶ F.alphaUpStarObjObj L := colimit.pre ((Subtype.mono_coe L.unop.openNhds).functor.op ⋙ F) (monoBaseChangeOpenNhds i.unop).functor.op

@[simp]
lemma alphaUpStarObjObj_ι_pre {K L : (Compacts X)ᵒᵖ} (i : L ⟶ K) (U : (L.unop.openNhds )ᵒᵖ ): F.alphaUpStarObjObj_ι U ≫ F.alphaUpStarObjMap i = F.alphaUpStarObjObj_ι ( (monoBaseChangeOpenNhds i.unop).functor.op.obj U) := by
  unfold alphaUpStarObjObj_ι alphaUpStarObjMap
  rw [← colimit.ι_pre]
  rfl

@[simp]
lemma alphaUpStarObjObj_ι_pre_assoc {K L : (Compacts X)ᵒᵖ} (i : L ⟶ K) (U : (L.unop.openNhds )ᵒᵖ ) { Z : A} (h : _ ⟶ Z): F.alphaUpStarObjObj_ι U ≫ F.alphaUpStarObjMap i ≫ h = F.alphaUpStarObjObj_ι ( (monoBaseChangeOpenNhds i.unop).functor.op.obj U) ≫ h := by
  rw [← Category.assoc, alphaUpStarObjObj_ι_pre]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simps]
def alphaUpStarObj (F : Presheaf A (of X)) : (Compacts X)ᵒᵖ ⥤ A where
  obj := F.alphaUpStarObjObj
  map  := F.alphaUpStarObjMap
  map_comp _ _ := by
    ext
    rw [← Category.assoc]
    aesop_cat

end TopCat.Presheaf

namespace CategoryTheory.NatTrans
variable [HasColimitsOfSize.{w, w} A ]

def alphaUpStarNatTransApp { F1 F2 : Presheaf A (of X)} (τ : F1 ⟶ F2) (K : (Compacts X)ᵒᵖ): F1.alphaUpStarObjObj K  ⟶ F2.alphaUpStarObjObj K := colimMap <| Functor.whiskerLeft _ τ

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma alphaUpStar_ι_NatTrans { F1 F2 : Presheaf A (of X)} (τ : F1 ⟶ F2) {K : (Compacts X)ᵒᵖ} (U : (K.unop.openNhds)ᵒᵖ) : F1.alphaUpStarObjObj_ι U ≫ τ.alphaUpStarNatTransApp K = τ.app (op U.unop.val) ≫ F2.alphaUpStarObjObj_ι U := by
  unfold Presheaf.alphaUpStarObjObj_ι alphaUpStarNatTransApp
  simp

@[simp]
lemma alphaUpStar_ι_NatTrans_assoc { F1 F2 : Presheaf A (of X)} (τ : F1 ⟶ F2) {K : (Compacts X)ᵒᵖ} (U : (K.unop.openNhds)ᵒᵖ) {Z : A} ( h : _ ⟶ Z): F1.alphaUpStarObjObj_ι U ≫ τ.alphaUpStarNatTransApp K ≫ h = τ.app (op U.unop.val) ≫ F2.alphaUpStarObjObj_ι U ≫ h:= by
  rw [← Category.assoc,alphaUpStar_ι_NatTrans, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
@[simps]
def alphaUpStarNatTrans {F1 F2 : Presheaf A (of X)} (τ : F1 ⟶ F2) : F1.alphaUpStarObj  ⟶ F2.alphaUpStarObj where
app := alphaUpStarNatTransApp τ
naturality _ _ _ := by
  apply F1.alphaUpStarObjObj_hom_ext-- je voudrais que ext marche
  intro
  rw [← Category.assoc, ← Category.assoc]
  simp;rfl

end CategoryTheory.NatTrans

namespace TopCat.Presheaf

variable [HasColimitsOfSize.{w, w} A ]

set_option backward.isDefEq.respectTransparency false in
@[simps]
def alphaUpStar : Presheaf A (of X) ⥤ KPresheaf A X where
  obj := alphaUpStarObj
  map := NatTrans.alphaUpStarNatTrans
  map_id _ := by
    ext
    apply alphaUpStarObjObj_hom_ext
    intro
    simp [CategoryStruct.id]

end TopCat.Presheaf


namespace TopCat.KPresheaf

variable [HasLimitsOfSize.{w, w} A] (G : KPresheaf A (of X)) {U : (Opens X)ᵒᵖ}

def alphaDownStarObjObj (U : (Opens X)ᵒᵖ ) : A := limit ((Subtype.mono_coe U.unop.compactInsd).functor.op ⋙ G)

def alphaDownStarObjObj_π (K : (U.unop.compactInsd )ᵒᵖ ) :  G.alphaDownStarObjObj U ⟶ G.obj (op K.unop.val) := limit.π ((Subtype.mono_coe U.unop.compactInsd).functor.op ⋙ G) _

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma alphaDownStarObjObj_w {K L : (U.unop.compactInsd)ᵒᵖ} (i : K ⟶ L) : G.alphaDownStarObjObj_π K ≫ G.map i = G.alphaDownStarObjObj_π L := by
  unfold alphaDownStarObjObj_π
  forceLimW

@[simp]
lemma alphaDownStarObjObj_w_assoc {K L : (U.unop.compactInsd)ᵒᵖ} (i : K ⟶ L) {Z : A} (h : _ ⟶ Z): G.alphaDownStarObjObj_π K ≫ G.map i ≫ h = G.alphaDownStarObjObj_π L ≫ h := by
  rw [← Category.assoc,alphaDownStarObjObj_w]

@[ext]
lemma alphaDownStarObjObj_hom_ext {Y : A} (f g : Y ⟶ G.alphaDownStarObjObj U) : (∀ K : (U.unop.compactInsd)ᵒᵖ, f ≫ G.alphaDownStarObjObj_π K = g ≫ G.alphaDownStarObjObj_π K ) → f = g := limit.hom_ext

def alphaDownStarObjMap {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) : G.alphaDownStarObjObj U ⟶ G.alphaDownStarObjObj V := limit.pre ((Subtype.mono_coe U.unop.compactInsd).functor.op ⋙ G) (monoBaseChangeCompactInsd i.unop).functor.op

@[simp]
lemma alphaDownStarObjObj_pre_π {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (K : (V.unop.compactInsd )ᵒᵖ ): G.alphaDownStarObjMap i ≫  G.alphaDownStarObjObj_π K = G.alphaDownStarObjObj_π ( (monoBaseChangeCompactInsd i.unop).functor.op.obj K) := by
  unfold alphaDownStarObjObj_π alphaDownStarObjMap
  rw [← limit.pre_π]
  rfl

@[simp]
lemma alphaDownStarObjObj_pre_π_assoc {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (K : (V.unop.compactInsd )ᵒᵖ ) {Z : A} (h : _ ⟶ Z): G.alphaDownStarObjMap i ≫  G.alphaDownStarObjObj_π K ≫ h = G.alphaDownStarObjObj_π ( (monoBaseChangeCompactInsd i.unop).functor.op.obj K) ≫ h:= by
  rw [← Category.assoc, alphaDownStarObjObj_pre_π]
  rfl

def alphaDownStarObjObj_lift {U : (Opens X)ᵒᵖ} (c : Cone <| (Subtype.mono_coe U.unop.compactInsd).functor.op ⋙ G) : c.pt ⟶ G.alphaDownStarObjObj U := limit.lift _ c

@[simp]
lemma alphaDownStarObjObj_lift_π {U : (Opens X)ᵒᵖ} (c : Cone <| (Subtype.mono_coe U.unop.compactInsd).functor.op ⋙ G) (K : (U.unop.compactInsd)ᵒᵖ): G.alphaDownStarObjObj_lift c
 ≫ G.alphaDownStarObjObj_π K = c.π.app K := limit.lift_π c K

 @[simp]
lemma alphaDownStarObjObj_lift_π_assoc {U : (Opens X)ᵒᵖ} (c : Cone <| (Subtype.mono_coe U.unop.compactInsd).functor.op ⋙ G) (K : (U.unop.compactInsd)ᵒᵖ) {Z : A} (h : _ ⟶ Z ): G.alphaDownStarObjObj_lift c
 ≫ G.alphaDownStarObjObj_π K ≫ h = c.π.app K ≫ h:= limit.lift_π_assoc c K _

set_option backward.isDefEq.respectTransparency false in
@[simps]
def alphaDownStarObj (G : KPresheaf A (of X)) : (Opens X)ᵒᵖ ⥤ A where
  obj := G.alphaDownStarObjObj
  map  := G.alphaDownStarObjMap

end TopCat.KPresheaf

namespace CategoryTheory.NatTrans
variable [HasLimitsOfSize.{w, w} A ]

def alphaDownStarNatTransApp { G1 G2 : KPresheaf A (of X)} (σ : G1 ⟶ G2) (U : (Opens X)ᵒᵖ): G1.alphaDownStarObjObj U  ⟶ G2.alphaDownStarObjObj U := limMap <| Functor.whiskerLeft _ σ

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma alphaDownStar_NatTrans_π { G1 G2 : KPresheaf A (of X)} (σ : G1 ⟶ G2) {U : (Opens X)ᵒᵖ} (K : (U.unop.compactInsd)ᵒᵖ) :  σ.alphaDownStarNatTransApp U ≫ G2.alphaDownStarObjObj_π K = G1.alphaDownStarObjObj_π K ≫ σ.app (op K.unop.val) := by
  unfold TopCat.KPresheaf.alphaDownStarObjObj_π alphaDownStarNatTransApp
  simp

@[simp]
lemma alphaDownStar_NatTrans_π_assoc { G1 G2 : KPresheaf A (of X)} (σ : G1 ⟶ G2) {U : (Opens X)ᵒᵖ} (K : (U.unop.compactInsd)ᵒᵖ) {Z : A} (h : Z ⟶ _) : (h ≫ σ.alphaDownStarNatTransApp U) ≫ G2.alphaDownStarObjObj_π K = (h ≫ G1.alphaDownStarObjObj_π K) ≫ σ.app (op K.unop.val) := by
  rw [ Category.assoc, alphaDownStar_NatTrans_π, ← Category.assoc]

set_option backward.isDefEq.respectTransparency false in
@[simps]
def alphaDownStarNatTrans {G1 G2 : KPresheaf A (of X)} (σ : G1 ⟶ G2) : G1.alphaDownStarObj  ⟶ G2.alphaDownStarObj where
app := alphaDownStarNatTransApp σ

end CategoryTheory.NatTrans

namespace TopCat.KPresheaf

variable [HasLimitsOfSize.{w, w} A ]

set_option backward.isDefEq.respectTransparency false in
@[simps]
def alphaDownStar : KPresheaf A X ⥤ Presheaf A (of X) where
  obj := alphaDownStarObj
  map := NatTrans.alphaDownStarNatTrans
  map_id _ := by
    apply NatTrans.ext
    ext
    apply alphaDownStarObjObj_hom_ext
    intro
    simp [CategoryStruct.id]
  map_comp _ _ := by
    apply NatTrans.ext
    ext
    apply alphaDownStarObjObj_hom_ext
    intro
    rw [ NatTrans.comp_app]
    slice_rhs 2 3 => rw [ NatTrans.alphaDownStarNatTrans_app,
      NatTrans.alphaDownStar_NatTrans_π]
    slice_rhs 1 2 => rw [ NatTrans.alphaDownStarNatTrans_app,
      NatTrans.alphaDownStar_NatTrans_π]
    simp

end TopCat.KPresheaf

namespace CategoryTheory.NatTrans

variable [HasColimitsOfSize.{w, w} A] [HasLimitsOfSize.{w, w} A]

open TopCat.KPresheaf TopCat.Presheaf
variable {F : Presheaf A (of X)} {G : KPresheaf A X} (τ : (alphaUpStar).obj F ⟶ G) (σ : F ⟶ (alphaDownStar).obj G) (K : Compacts X) (U : Opens X)

set_option backward.isDefEq.respectTransparency false in
@[simps]
def toFtoαGConeπ : (Functor.const (Subtype U.compactInsd)ᵒᵖ).obj (F.obj (op U)) ⟶ (Subtype.mono_coe U.compactInsd).functor.op ⋙ G where
  app K := F.alphaUpStarObjObj_ι (K := op (K.unop.val)) ( op K.unop.toOpenNhds) ≫ τ.app (op K.unop.val)
  naturality {K L} i := by
    rw [Functor.comp_map, Category.assoc, ← τ.naturality]
    simp;rfl

@[simps]
def toFtoαGCone : Cone <| (Subtype.mono_coe U.compactInsd).functor.op ⋙ G := Cone.mk _ (τ.toFtoαGConeπ _ )

set_option backward.isDefEq.respectTransparency false in
@[simps]
def toFtoαG : F ⟶ alphaDownStar.obj G where
  app U := alphaDownStarObjObj_lift _ (τ.toFtoαGCone U.unop)
  naturality {U V} i := by
    apply alphaDownStarObjObj_hom_ext
    intro K
    simp
    unfold alphaUpStarObjObj_ι
    forceColimW

    /- --tout le bazard qui suit c'est parceque les lemmes en _w n'ont pas la bonne forme...

    let W := (op (unop K).toOpenNhds)
    let Z : (↑((unop K).val).openNhds)ᵒᵖ:= (op (Subtype.toOpenNhds (i.unop.baseChangeCompactInsd (unop K))))



    #check F.alphaUpStarObjObj_w (K := op K.unop.val) (U := W) (V := Z) ⟨by
      unfold W Z
      simp
      apply?
      simp at Z
      sorry⟩
    erw [F.alphaUpStarObjObj_w_assoc _ (τ.app (op (unop K).val))]
    unfold alphaUpStarObjObj_ι
    forceColimW-/

set_option backward.isDefEq.respectTransparency false in
@[simps]
def toαFtoGCoconeι : (Subtype.mono_coe K.openNhds).functor.op ⋙ F ⟶ (Functor.const (Subtype K.openNhds)ᵒᵖ).obj (G.obj (op K))  where
  app U := σ.app _ ≫ G.alphaDownStarObjObj_π (U := op (U.unop.val)) (op U.unop.toCompactInsd)

@[simps]
def toαFtoGCocone : Cocone <| (Subtype.mono_coe K.openNhds).functor.op ⋙ F := Cocone.mk _ (σ.toαFtoGCoconeι _ )

set_option backward.isDefEq.respectTransparency false in
@[simps]
def toαFtoG : alphaUpStar.obj F ⟶ G where
  app K := F.alphaUpStarObjObj_desc  (σ.toαFtoGCocone _)
  naturality {K L} i := by
    apply alphaUpStarObjObj_hom_ext
    intro U
    simp
    unfold alphaDownStarObjObj_π
    forceLimW

end NatTrans

--namespace TopCat.KPresheaf-- ça fait des trucs bizzares avec homEquiv

open TopCat.Presheaf TopCat.KPresheaf

variable [HasColimitsOfSize.{w, w, v, u} A] [HasLimitsOfSize.{w, w, v, u} A] (F : Presheaf A (of X)) (G : KPresheaf A X)

set_option backward.isDefEq.respectTransparency false in
/-- The bijection between hom(αF, G) and hom(F,αG) -/
def homEquivAlpha: (alphaUpStar.obj F ⟶ G) ≃ ( F ⟶ alphaDownStar.obj G) where
  toFun := fun τ => τ.toFtoαG
  invFun := fun σ  => σ.toαFtoG
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
