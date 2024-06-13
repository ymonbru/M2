import Mathlib
import Mathlib.Topology.Separation

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite

variable (X) [TopologicalSpace X] [T2Space X]
variable (K:Compacts X)
variable (F:(Opens X)ᵒᵖ⥤ Ab)


--α^*

def KsubU : Set (Opens X) := fun (U:Opens X) => (K.carrier ⊆ U.carrier) --∧ IsCompact (closure U.carrier) peut être?

def KsubU_cat : Type := FullSubcategory (KsubU X K)

instance : Category (KsubU_cat X K) := FullSubcategory.category (KsubU X K)

def FU : (KsubU_cat X K)ᵒᵖ ⥤ Ab := Functor.comp (fullSubcategoryInclusion (KsubU X K)).op  F

variable (K1 K2:Compacts X) (f:K1⟶ K2)

def K1subK2subU : (KsubU_cat X K2) ⥤ (KsubU_cat X K1) where
  obj W:=(⟨W.obj,Set.Subset.trans (leOfHom f) W.property⟩:KsubU_cat X K1)
  map := by
    intro U V F
    exact homOfLE (leOfHom F)

def K1subK2natTrans : (FU X K2 F) ⟶  (Functor.comp (K1subK2subU X K1 K2 f).op (FU X K1 F)) where
  app W := by
    exact 𝟙 _

noncomputable section

def AlphaUpStarF :(Compacts X)ᵒᵖ ⥤ Ab  where
  obj K := colimit (FU X K.unop F)
  map f:= colimMap (K1subK2natTrans X F _ _ f.unop) ≫ (colimit.pre (FU X _ F) (K1subK2subU X _ _ f.unop).op)
  map_id := by
    intro _
    apply colimit.hom_ext
    simp
    intro _
    rfl
  map_comp := by
    intro _ _ _ _ _
    simp
    apply colimit.hom_ext
    simp
    intro _
    rfl

variable (F1:(Opens X)ᵒᵖ⥤ Ab) (F2:(Opens X)ᵒᵖ⥤ Ab) (τ :F1 ⟶ F2)

def τres :(FU X K F1)⟶ (FU X K F2) where
  app U:= τ.app (op (U.unop.obj))
  naturality := by
    unfold FU
    simp [τ.naturality]


#check (Cocones.precompose (τres X K F1 F2 τ))

#check colimit.desc (FU X K F1) ((Cocones.precompose (τres X K F1 F2 τ)).obj (getColimitCocone (FU X K F2)).cocone)

#check (Cocones.precompose (τres X K F1 F2 τ)).obj (getColimitCocone (FU X K F2)).cocone

def AlphaUpStarTau : (AlphaUpStarF X F1) ⟶ (AlphaUpStarF X F2) where
  app K := colimit.desc (FU X K.unop F1) ((Cocones.precompose (τres X K.unop F1 F2 τ)).obj (getColimitCocone (FU X K.unop F2)).cocone)
  naturality := by
    intro K1 K2 f
    apply colimit.hom_ext
    intro U
    simp
    unfold τres
    simp
    sorry


def AlphaUpStar :((Opens X)ᵒᵖ ⥤ Ab)⥤ ((Compacts X)ᵒᵖ ⥤ Ab) where
  obj F:= AlphaUpStarF X F
  map τ := AlphaUpStarTau X _ _ τ
  map_id:= by
    intro F
    simp
    unfold AlphaUpStarTau Cocones.precompose τres
    simp
    --rfl
    
    sorry
  map_comp:= by
    intro F1 F2 F3 f g
    
    simp
    sorry









--α_*
variable (U:Opens X) (G:(Compacts X)ᵒᵖ ⥤ Ab)

def UsupK : Set (Compacts X) := fun (K:Compacts X) => (K.carrier ⊆ U.carrier) --∧ IsCompact (closure U.carrier) peut être?

def UsupK_cat : Type := FullSubcategory (UsupK X U)

instance : Category (UsupK_cat X U) := FullSubcategory.category (UsupK X U)

def GK : (UsupK_cat X U)ᵒᵖ ⥤ Ab := Functor.comp (fullSubcategoryInclusion (UsupK X U)).op  G

variable (U1 U2 :Opens X) (f:U1⟶ U2)

def U2supU1supK : (UsupK_cat X U1) ⥤ (UsupK_cat X U2) where
  obj W:=(⟨W.obj,Set.Subset.trans W.property (leOfHom f)⟩:UsupK_cat X U2)
  map := by
    intro U V F
    exact homOfLE (leOfHom F)

def U2supU1natTrans : (GK X U1 G) ⟶  (Functor.comp (U2supU1supK X U1 U2 f).op (GK X U2 G)) where
  app W := by
    exact 𝟙 _

noncomputable

def AlphaDownStar :(Opens X)ᵒᵖ ⥤ Ab  where
  obj U := limit (GK X U.unop G)
  map f:= (limit.pre (GK X _ G) (U2supU1supK X _ _ f.unop).op) ≫ limMap (U2supU1natTrans X G _ _ f.unop)
  map_id := by
    intro _
    apply limit.hom_ext
    simp
    intro _
    rfl
  map_comp := by
    intro _ _ _ _ _
    simp
    apply limit.hom_ext
    intro _
    simp
    rfl

--Adjunction

--#check (AlphaUpStar X _) ⊣ (AlphaDownStar X _)
