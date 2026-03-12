import M2.Propre.KSheaf
import M2.forceColimW
import Mathlib.Topology.Sheaves.Sheaf

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite TopCat

universe u v w

variable {X : Type w} [TopologicalSpace X]
variable {A : Type u} [Category.{v, u} A] [HasColimitsOfSize.{w, w} A] [HasLimitsOfSize.{w, w} A ]

/-def baseChangeCompactNhds {K L : Compacts X} (h : K.carrier ⊆ L.carrier) : L.compactNhds → K.compactNhds := fun M => ⟨M.1, fun ⟨x,hx⟩ => M.2 ⟨x, h hx ⟩⟩

lemma monoBaseChangeCompactNhds {K L : Compacts X} (h : K.carrier ⊆ L.carrier) : Monotone <| baseChangeCompactNhds h := fun _ _ hyp => fun _ hx => hyp hx-/


def Quiver.Hom.baseChangeOpenNhds {K L : Compacts X} (h : K ⟶ L) : L.openNhds → K.openNhds := fun ⟨U,hU⟩ => ⟨U, fun _ hx => Set.mem_of_subset_of_mem hU (leOfHom h hx)⟩

lemma monoBaseChangeOpenNhds {K L : Compacts X} (h : K ⟶ L) : Monotone <| h.baseChangeOpenNhds := fun  _ _ hUV _ hx => SetLike.mem_coe.mpr (hUV hx)

def Quiver.Hom.baseChangeCompactsInsd {U V : Opens X} (h : U ⟶ V) : U.compactsInsd → V.compactsInsd := fun ⟨K,hK⟩ => ⟨K, fun _ hx => by
  apply Set.mem_of_subset_of_mem (leOfHom h) (hK hx)⟩

lemma monoBaseChangeCompactsInsd {U V : Opens X} (h : U ⟶ V) : Monotone <| h.baseChangeCompactsInsd := fun  _ _ hKL _ hx => SetLike.mem_coe.mpr (hKL hx)

noncomputable section
namespace TopCat.Presheaf

@[simps]
def alphaUpStarObj (F : Presheaf A (of X)): (Compacts X)ᵒᵖ ⥤ A where
  obj K := colimit ((Subtype.mono_coe K.unop.openNhds).functor.op ⋙ F)
  map {K L} i := colimit.pre ((Subtype.mono_coe L.unop.openNhds).functor.op ⋙ F) (monoBaseChangeOpenNhds i.unop).functor.op
  map_id _ := by
    apply colimit.hom_ext
    intro
    rw [CategoryTheory.Limits.colimit.ι_pre]
    exact Eq.symm (Category.comp_id _)-- pourquoi ça ne marche pas tout seul?
  map_comp {K L M} f g := by

    apply colimit.hom_ext
    intro U
    rw [colimit.ι_pre]
    --ça il faut le forcer avec une tactique

    let Eforce := (monoBaseChangeOpenNhds f.unop).functor.op
    let Fforce := (Subtype.mono_coe (unop L).openNhds).functor.op ⋙ F
    let kforce := U

    --have : Eforce ⋙ Fforce = (monoBaseChangeOpenNhds (f ≫ g).unop).functor.op ⋙ (Subtype.mono_coe (unop M).openNhds).functor.op ⋙ F := by rfl
    --ici il arrive à identifier Eforce ⋙ Fforce, mais il ne devrait pas en général→ en fait si?
    slice_rhs 1 2 => erw [ colimit.ι_pre Fforce Eforce _]

    unfold Fforce Eforce

    let Eforce := (monoBaseChangeOpenNhds g.unop).functor.op
    let Fforce := (Subtype.mono_coe (unop M).openNhds).functor.op ⋙ F
    let kforce := (monoBaseChangeOpenNhds f.unop).functor.op.obj U

    erw [ colimit.ι_pre Fforce Eforce _]

    rfl

@[simps]
def alphaUpStarNatTrans { F1 F2 : Presheaf A (of X)} (τ : F1 ⟶ F2) : F1.alphaUpStarObj  ⟶ F2.alphaUpStarObj where
app K := colimMap <| Functor.whiskerLeft _ τ
naturality K L i:= by
  apply colimit.hom_ext
  intro
  simp only [Functor.comp_obj, Functor.op_obj, Monotone.functor_obj, alphaUpStarObj_obj, alphaUpStarObj_map, ι_colimMap_assoc, Functor.whiskerLeft_app]
  -- par une tactique (sinon ça cassera)
  let Eforce := (alphaUpStarObj._proof_3 i).functor.op
  let Fforce := (alphaUpStarObj._proof_1 L).functor.op ⋙ F1

  slice_lhs 1 2 => erw [colimit.ι_pre Fforce Eforce]
  unfold Fforce Eforce

  --re tactique
  let Eforce := (alphaUpStarObj._proof_3 i).functor.op
  let Fforce := (alphaUpStarObj._proof_1 L).functor.op ⋙ F2

  slice_rhs 2 3 => erw [colimit.ι_pre Fforce Eforce]
  unfold Fforce Eforce

  simp;rfl

def alphaUpStar : Presheaf A (of X) ⥤ KPresheaf A X where
  obj := alphaUpStarObj
  map := alphaUpStarNatTrans
  map_id _ := by
    ext
    apply colimit.hom_ext
    intro
    simp only [Functor.comp_obj, Functor.op_obj, Monotone.functor_obj, alphaUpStarObj_obj, alphaUpStarNatTrans_app, ι_colimMap, Functor.whiskerLeft_app, NatTrans.id_app, Category.comp_id]
    forceColimW
    · exact 𝟙 _
    · unfold CategoryStruct.id fForce ;simp;rfl


end TopCat.Presheaf


namespace TopCat.KPresheaf

@[simps]
def alphaDownStarObj (G : KPresheaf A X): (Opens X)ᵒᵖ ⥤ A where
  obj U := limit ((Subtype.mono_coe U.unop.compactsInsd).functor.op ⋙ G)
  map {U V} i:= limit.pre ((Subtype.mono_coe U.unop.compactsInsd).functor.op ⋙ G) ( monoBaseChangeCompactsInsd i.unop).functor.op
  map_comp {U V W} i j := by
    ext K
    rw [limit.pre_π]

    --avec tactique
    let Eforce := (monoBaseChangeCompactsInsd j.unop).functor.op
    let Fforce := (Subtype.mono_coe (unop V).compactsInsd).functor.op ⋙ G
    slice_rhs 2 3 => erw [ limit.pre_π Fforce Eforce]

    erw [limit.pre_π]
    rfl

@[simps]
def alphaDownStarNatTrans { G1 G2 : KPresheaf A X} (τ : G1 ⟶ G2) : G1.alphaDownStarObj  ⟶ G2.alphaDownStarObj where
app K := limMap <| Functor.whiskerLeft _ τ
naturality {U V i}:= by
  apply limit.hom_ext
  intro
  simp only [alphaDownStarObj_obj, Functor.comp_obj, Functor.op_obj, Monotone.functor_obj, alphaDownStarObj_map, Category.assoc, limMap_π, Functor.whiskerLeft_app]

  erw [limit.pre_π]

  slice_lhs 1 2  => erw [limit.pre_π]
  simp
  rfl

def alphaDownStar : KPresheaf A X ⥤ Presheaf A (of X) where
  obj := alphaDownStarObj
  map := alphaDownStarNatTrans
  map_id _ := by
    apply NatTrans.ext
    ext
    apply limit.hom_ext
    intro
    simp [CategoryStruct.id]
  map_comp _ _ := by
    apply NatTrans.ext
    ext
    rw [NatTrans.comp_app]
    apply limit.hom_ext
    intro
    simp


end TopCat.KPresheaf

namespace CategoryTheory.NatTrans

open TopCat.KPresheaf TopCat.Presheaf
variable {F : Presheaf A (of X)} {G : KPresheaf A X} (τ : (alphaUpStar).obj F ⟶ G) (σ : F ⟶ (alphaDownStar).obj G) (K : Compacts X) (U : Opens X)

@[simps]
def toFtoαGConeπ : (Functor.const (Subtype U.compactsInsd)ᵒᵖ).obj (F.obj (op U)) ⟶ (Subtype.mono_coe U.compactsInsd).functor.op ⋙ G where
  app K := (colimit.ι ((alphaUpStarObj._proof_1 (op (unop K).val)).functor.op ⋙ F) (op K.unop.toOpenNhds)) ≫ τ.app (op K.unop.val)
  naturality {K L} i := by
    simp only [Functor.const_obj_obj, Functor.comp_obj, Functor.op_obj, Monotone.functor_obj,
      Functor.const_obj_map, Category.id_comp, Functor.comp_map, Functor.op_map, Category.assoc]
    rw [← τ.naturality, ← Category.assoc]
    apply eq_whisker
    simp [alphaUpStar]

    let Fforce := (alphaUpStarObj._proof_1 (op (unop L).val)).functor.op ⋙ F
    let Eforce := (alphaUpStarObj._proof_3 ((Subtype.mono_coe U.compactsInsd).functor.map i.unop).op).functor.op

    erw [colimit.ι_pre Fforce Eforce];rfl

@[simps]
def toFtoαGCone : Cone <| (Subtype.mono_coe U.compactsInsd).functor.op ⋙ G := Cone.mk _ (τ.toFtoαGConeπ _ )

def toFtoαG : F ⟶ alphaDownStar.obj G where
  app U := limit.lift _ (τ.toFtoαGCone U.unop)
  naturality {U V} i := by
    apply limit.hom_ext
    intro K
    simp [alphaDownStar]
    sorry

@[simps]
def toαFtoGCoconeι : (Subtype.mono_coe K.openNhds).functor.op ⋙ F ⟶ (Functor.const (Subtype K.openNhds)ᵒᵖ).obj (G.obj (op K))  where
  app K := by
    apply σ.app _ ≫ _

    simp
    sorry
  naturality {K L} i := by sorry

@[simps]
def toαFtoGCocone : Cocone <| (Subtype.mono_coe K.openNhds).functor.op ⋙ F := Cocone.mk _ (σ.toαFtoGCoconeι _ )

def toαFtoG : alphaUpStar.obj F ⟶ G where
  app K := colimit.desc _ (σ.toαFtoGCocone K.unop)
  naturality {U V} i := by sorry

/-- The bijection between hom(αF, G) and hom(F,αG) -/
@[simps]
def homEquiv: (alphaUpStar.obj F ⟶ G) ≃ ( F ⟶ alphaDownStar.obj G) where
  toFun := fun τ => τ.toFtoαG
  invFun := fun σ  => σ.toαFtoG
  left_inv τ := sorry
  right_inv σ := sorry


/-- The data necessary to build the adjunction between α^* and α_*-/
@[simps]
def adjthm : Adjunction.CoreHomEquiv (alphaUpStar (A := A) (X := X)) alphaDownStar where
homEquiv := sorry
homEquiv_naturality_left_symm _ _ := by sorry
homEquiv_naturality_right _ _ := by sorry

/-- The adjunction between α^* and α_*-/
@[simps!]
def AdjAlphaStar : (alphaUpStar (A := A) (X := X)) ⊣ (alphaDownStar ) := Adjunction.mkOfHomEquiv (adjthm)
