import Mathlib
import Mathlib.Topology.Separation
import M2.Ksheaves

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite

variable {X} [TopologicalSpace X] --[T2Space X]

--α^*
noncomputable section
variable (K:Compacts X)
variable (F:(Opens X)ᵒᵖ⥤ Ab)
variable (P:Opens X → Prop)-- true pour le alpha normal et IsCompact (closure U.carrier) pour la version relativement compacte

def KsubU : Set (Opens X) := fun U : Opens X ↦ (K : Set X) ⊆ U ∧ P U

def KsubU_cat : Type := FullSubcategory (KsubU K P)

/-instance : SetLike (KsubU_cat X K P) X where
  coe U := U.obj.carrier

  coe_injective' := fun ⟨_ , _ ⟩ ⟨_, _⟩ h => by
    apply FullSubcategory.ext
    simp at h
    exact h-/


instance : Category (KsubU_cat K P) := FullSubcategory.category (KsubU K P)

@[simps!]
def FU : (KsubU_cat K P)ᵒᵖ ⥤ Ab := (fullSubcategoryInclusion <| KsubU K P).op.comp  F

variable {K₁ K₂ : Compacts X} (f : K₁ ⟶ K₂)

@[simps]
def K₁subK₂subU : (KsubU_cat K₂ P) ⥤ (KsubU_cat K₁ P) where
  obj W := ⟨W.obj, Set.Subset.trans (leOfHom f) W.property.1, W.property.2⟩
  map {U V} F := homOfLE (leOfHom F)

@[simps]
def K₁subK₂natTrans : FU K₂ F P ⟶  (Functor.comp (K₁subK₂subU P f).op (FU K₁ F P)) where
  app W := 𝟙 _

attribute [local aesop safe (rule_sets := [CategoryTheory])] colimit.hom_ext limit.hom_ext

@[simps]
def AlphaUpStarF : (Compacts X)ᵒᵖ ⥤ Ab  where
  obj K := colimit (FU K.unop F P)
  map f := colimMap (K₁subK₂natTrans F P f.unop) ≫ (colimit.pre (FU _ F P) (K₁subK₂subU P f.unop).op)

variable {F1 F2 : (Opens X)ᵒᵖ ⥤ Ab} (τ : F1 ⟶ F2)

@[simps]
def τres : FU K F1 P ⟶ FU K F2 P where
  app U := τ.app <| op U.unop.obj
  naturality := by simp [FU, τ.naturality]

@[simps]
def AlphaUpStarTau : AlphaUpStarF F1 P ⟶ AlphaUpStarF F2 P where
  app K := colimMap (τres K.unop P τ)

@[simps]
def AlphaUpStarP : ((Opens X)ᵒᵖ ⥤ Ab) ⥤ ((Compacts X)ᵒᵖ ⥤ Ab) where
  obj F := AlphaUpStarF F P
  map τ := AlphaUpStarTau P τ
  map_id F := by
    ext : 2 -- Le problème si on ne mets pas le : 2 est que ext part dans la mauvaise direction
            -- en appliquant `AddCommGrp.ext` plutôt que `colimit.hom_ext`.
            -- Avec un
            -- attribute [-ext] AddCommGrp.ext
            -- Il trouve encore autre chose. Il serait bon de discuter de ça avec Joël
    aesop_cat
  map_comp {_ _ _} _ _ := by
    ext : 2
    aesop_cat


variable (X)

def trueCond: Opens X → Prop :=  fun _ ↦ true

@[simps!]
def AlphaUpStar : ((Opens X)ᵒᵖ ⥤ Ab) ⥤ ((Compacts X)ᵒᵖ ⥤ Ab) := AlphaUpStarP (trueCond X)

end

noncomputable section
--α_*
variable (U:Opens X) (G:(Compacts X)ᵒᵖ ⥤ Ab)

def UsupK : Set (Compacts X) := fun K : Compacts X => (K : Set X) ⊆ U.carrier --∧ IsCompact (closure U.carrier) peut être?

def UsupK_cat : Type := FullSubcategory (UsupK U)

instance : Category (UsupK_cat U) := FullSubcategory.category (UsupK U)

@[simps!]
def GK : (UsupK_cat U)ᵒᵖ ⥤ Ab := Functor.comp (fullSubcategoryInclusion (UsupK U)).op  G

variable {U1 U2 : Opens X} (f : U1⟶ U2)

@[simps]
def U2supU1supK : (UsupK_cat U1) ⥤ (UsupK_cat U2) where
  obj W := ⟨W.obj, W.property.trans (leOfHom f)⟩
  map   := by aesop

@[simps]
def U2supU1natTrans : (GK U1 G) ⟶  (Functor.comp (U2supU1supK f).op (GK U2 G)) where
  app W := 𝟙 _

-- bizarrement, aesop n’a pas l’air d’aimer `limit.hom_ext` même si on l’ajoute aux règles
-- il serait bien d’essayer de comprendre ça.

@[simps]
def AlphaDownStarG :(Opens X)ᵒᵖ ⥤ Ab  where
  obj U := limit (GK U.unop G)
  map f := (limit.pre (GK _ G) (U2supU1supK f.unop).op) ≫ limMap (U2supU1natTrans G f.unop)
  map_id _ := limit.hom_ext (by aesop)
  map_comp {_ _ _} _ _ := limit.hom_ext (by aesop)

variable (G1:(Compacts X)ᵒᵖ⥤ Ab) (G2:(Compacts X)ᵒᵖ⥤ Ab) (σ :G1 ⟶ G2)

@[simps]
def σres : GK U G1 ⟶ GK U G2 where
  app K := σ.app <| op K.unop.obj

@[simps]
def AlphaDownStarSigma : (AlphaDownStarG G1) ⟶ (AlphaDownStarG G2) where
  app U := limMap (σres U.unop G1 G2 σ )
  naturality _ _ _ := limit.hom_ext (by aesop)

variable (X)

@[simps]
def AlphaDownStar : ((Compacts X)ᵒᵖ ⥤ Ab) ⥤ ((Opens X)ᵒᵖ ⥤ Ab) where
  obj G := AlphaDownStarG G
  map σ := AlphaDownStarSigma _ _ σ
  map_id G := by
    ext : 2
    apply limit.hom_ext
    simp
  map_comp {_ _ _} _ _ := by
    ext : 2
    apply limit.hom_ext
    simp
end

--Adjunction

variable {F : (Opens X)ᵒᵖ ⥤ Ab} {G:(Compacts X)ᵒᵖ ⥤ Ab}
         (τ : (AlphaUpStar X).obj F ⟶ G) (σ : F ⟶ (AlphaDownStar X).obj G)
         (K : Compacts X) (U : Opens X)

noncomputable section

@[simps]
def ConeFtoAG_NT: (Functor.const (UsupK_cat U)ᵒᵖ).obj (F.obj { unop := U }) ⟶ GK U G where
  app L := colimit.ι (FU (fullSubcategoryInclusion _ |>.op.obj L).unop F <| trueCond X)
                     (op ⟨U,L.unop.property,rfl⟩) ≫ τ.app _
  naturality := by
    intro K L f
    unfold GK
    simp
    rw [← (τ.naturality _)]
    unfold AlphaUpStar AlphaUpStarP AlphaUpStarF K₁subK₂natTrans K₁subK₂subU
    simp

@[simps]
def ConeFtoAG : Cone (GK U G) where
  pt := F.obj (op U)
  π  := ConeFtoAG_NT τ U

@[simps]
def FtoAG : F ⟶ (AlphaDownStar X).obj G where
  app U := limit.lift _ (ConeFtoAG τ U.unop)
  naturality U V f := by
    apply limit.hom_ext
    intro K
    simp
    rw [← Category.assoc, ← colimit.w_assoc]
    rfl

@[simps]
def CoconeAFtoG_NT: FU K F P ⟶ (Functor.const (KsubU_cat K P)ᵒᵖ).obj (G.obj <| op K)  where
  app W :=  σ.app ((fullSubcategoryInclusion (KsubU K P)).op.obj W) ≫
    limit.π (GK ((fullSubcategoryInclusion (KsubU K P)).op.obj W).unop G)
            (op ⟨K, W.unop.property.1⟩) ≫ 𝟙 _
  naturality K L f := by simp; rfl

@[simps]
def CoconeAFtoG : Cocone (FU K F P) where
  pt := G.obj (op K)
  ι  := CoconeAFtoG_NT σ K

@[simps]
def AFtoG : (AlphaUpStar X).obj F ⟶ G where
  app K := colimit.desc _ (CoconeAFtoG σ K.unop)
  naturality K L f := by
    apply colimit.hom_ext
    intro V
    simp [AlphaUpStar]
    rw [← limit.w]
    rfl

@[simps]
def homEquiv : ((AlphaUpStar X).obj F ⟶ G) ≃ (F ⟶ (AlphaDownStar X).obj G) where
  toFun := fun τ ↦ FtoAG τ
  invFun := fun σ ↦ AFtoG σ
  left_inv σ := by
    ext : 2
    apply colimit.hom_ext
    aesop
  right_inv τ := by
    ext : 2
    apply limit.hom_ext
    aesop

def adjthm : Adjunction.CoreHomEquiv (AlphaUpStar X) (AlphaDownStar X) where
  homEquiv _ _ := homEquiv
  homEquiv_naturality_left_symm {_ _ _} _ _ := by
    ext : 2
    apply colimit.hom_ext
    intro _
    simp [homEquiv, AlphaUpStar]
  homEquiv_naturality_right {F G1 G2} τ σ := by
    ext : 2
    apply limit.hom_ext
    intro K
    simp [homEquiv, AlphaDownStar]

def AdjAlphaStar : (AlphaUpStar X ) ⊣ (AlphaDownStar X ) := .mkOfHomEquiv adjthm
