import M2.Ksheaves
import M2.KsubU
import M2.forceColimW
import M2.forceLimW
import M2.Suffices

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite

universe u v w

variable {X : Type w} [TopologicalSpace X]
variable {C : Type u} [Category.{v, u} C] [HasColimitsOfSize.{w, w} C] [HasLimitsOfSize.{w, w} C]

--α^*
noncomputable section
variable (K : Compacts X)
variable (F : (Opens X)ᵒᵖ ⥤ C)
variable (P : Opens X → Prop := trueCond)

/-- The natural transformation of change of basis for the diagram FU-/
@[simps!]
def K1subK2natTrans {K₁ K₂ : Compacts X} (f : K₁ ⟶ K₂) : (FU _ F P) ⟶  (K1subK2subU _ f).op ⋙ (FU _ F _) := 𝟙 _

/-- The functor α^*F-/
@[simps]
def AlphaUpStarF : (Compacts X)ᵒᵖ ⥤ C  where
  obj K := colimit (FU K.unop F P)
  map f := colimMap ((K1subK2natTrans F P f.unop)) ≫ (colimit.pre (FU _ _ _) (K1subK2subU _ _ ).op)

variable {F₁ F₂ : (Opens X)ᵒᵖ ⥤ C} (τ : F₁ ⟶ F₂)

/-- The restriction of the natural transformation between the digram FU over K₁ eand FU over K₂ -/
@[simps]
def τres : (FU K F₁ P) ⟶ (FU _ F₂ _) where
  app U := τ.app <| op (U.unop.obj)-- supprimer ça pose des problemes plsu tard dans RCalpha

/-- The natural transformation α^* τ between α^* F₁ and α^* F₂-/
@[simps]
def AlphaUpStarTau : (AlphaUpStarF F₁ P) ⟶ (AlphaUpStarF F₂ P) where
  app K := colimMap (τres K.unop P τ)

/-- The functor α^* with the conditon P-/
@[simps]
def AlphaUpStarP : ((Opens X)ᵒᵖ ⥤ C) ⥤ (Compacts X)ᵒᵖ ⥤ C where
  obj _ := AlphaUpStarF _ _
  map := AlphaUpStarTau P

/-- The first version of α^* -/
@[simps!]
def AlphaUpStar : ((Opens X)ᵒᵖ ⥤ C) ⥤ ((Compacts X)ᵒᵖ ⥤ C) := AlphaUpStarP

end

noncomputable section
--α_*

variable (U : Opens X) (G : (Compacts X)ᵒᵖ ⥤ C)

/-- The condition over compacts subset of being contained in U -/
def UsupK : Set (Compacts X) := fun (K : Compacts X) => (K : Set X) ⊆ U

/-- The category induced by UsupK -/
def UsupK_cat : Type w := ObjectProperty.FullSubcategory (UsupK U)

instance : Category (UsupK_cat U) := ObjectProperty.FullSubcategory.category (UsupK U)

instance : Bot (UsupK_cat U) := by
  use ⊥
  simp only [UsupK, coe_bot, Set.empty_subset]

/-- The conversion from an open that contain K to a compact contained in U-/
@[simps]
def KsubUToUsupK {K : Compacts X} {P : Opens X → Prop} (U : KsubU_cat K P) : UsupK_cat U.obj := ⟨K, U.property.1⟩

/-- The conversion from a compact contained in U to an open cotained in K-/
@[simps]
def UsupKToKsubU {U : Opens X} (K : UsupK_cat U) : KsubU_cat K.obj := ⟨U, K.property,rfl⟩

/-- The diagrom obtained by restricting G to the subcategory UsupK-/
@[simps!]
def GK : (UsupK_cat U)ᵒᵖ ⥤ C := Functor.comp (ObjectProperty.ι (UsupK U)).op  G

variable (U₁ U₂ : Opens X) (f : U₁ ⟶ U₂)-- U₁ ⊆ U₂

/-- The functor that sends compacts contained  in U₁ to compaccts contained in U₂-/
@[simps]
def U2supU1supK : (UsupK_cat U₁) ⥤ (UsupK_cat U₂) where
  obj W := (⟨W.obj,Set.Subset.trans W.property (leOfHom f)⟩ : UsupK_cat _)
  map i := ⟨homOfLE (leOfHom i.hom)⟩
/-
/-- The natural transformation of change of basis for the diagram GK-/
@[simps]
def U2supU1natTrans : (GK _ G) ⟶  Functor.comp (U2supU1supK _ _ f).op (GK _ G) where
  app _ := 𝟙 _-/

/-- The functor α_* G-/
@[simps]
def AlphaDownStarG : (Opens X)ᵒᵖ ⥤ C  where
  obj U := limit (GK U.unop G)
  map f := (limit.pre (GK _ G) (U2supU1supK _ _ f.unop).op) ≫ limMap (𝟙 _)--((U2supU1natTrans G _ _ f.unop))
-- c'est assez fou parceque sans le limMap il ne trouve pas seul

variable (G₁ G₂:(Compacts X)ᵒᵖ ⥤ C) (σ : G₁ ⟶ G₂)

/-- The natural transformation induced by σ between the two diagrams-/
@[simps]
def σres : (GK U G₁) ⟶ (GK _ G₂) where
  app K:= σ.app (op (K.unop.obj))

/-- The natural transformation α_* σ between α_* G₁ and /alpha_*G₂ -/
@[simps]
def AlphaDownStarSigma : (AlphaDownStarG G₁) ⟶ (AlphaDownStarG G₂) where
  app U := limMap <| σres U.unop _ _ σ

/-- The functor α_*-/
@[simps]
def AlphaDownStar : ((Compacts X)ᵒᵖ ⥤ C) ⥤ (Opens X)ᵒᵖ ⥤ C where
  obj _ := AlphaDownStarG _
  map := AlphaDownStarSigma _ _

end

--Adjunction

noncomputable section

variable {F : (Opens X)ᵒᵖ⥤ C} {G : (Compacts X)ᵒᵖ ⥤ C} (τ : (AlphaUpStar).obj F ⟶ G) (σ : F ⟶ (AlphaDownStar).obj G) (K : Compacts X) (U : Opens X)

/-- The naturals maps from F(U) to the family of G(K) for K contained in U-/
@[simps]
def ConeFtoAGπ : (Functor.const _ ).obj (F.obj (op U)) ⟶ GK U G where
  app L := colimit.ι (FU (ObjectProperty.ι _ |>.op.obj _ ).unop _ ) (op ⟨U,L.unop.property,rfl⟩) ≫ τ.app _

  naturality _ L _ := by
    suffices _ = colimit.ι (FU _ _ _ ) (op ⟨U , _ ⟩) ≫ τ.app (op _ ) ≫ G.map _ by simpa
    rw [← (τ.naturality _)]
    simp [ K1subK2subU]

/-- The cone of the diragram GK U with point F(U)-/
@[simps]
def ConeFtoAG : Cone (GK U G) := Cone.mk _ (ConeFtoAGπ τ _)

/-- The natural transformation from F to α_*G induced taking the natural map from ConeFtoAG to the colimit-/
@[simps]
def FtoAG : F ⟶ (AlphaDownStar).obj G where
  app U := limit.lift _ (ConeFtoAG τ U.unop)
  naturality U V f := by
    --ext ne trouve pas limit.hom_ext
    apply limit.hom_ext
    intro _
    suffices F.map f ≫ colimit.ι (FU _ F) (op { obj := unop V, property := _ }) ≫ τ.app _ = colimit.ι (FU _ F) (op { obj := unop U, property := _ }) ≫ τ.app (op _) by simpa
    forceColimW


/-- The naturals maps from the family of F(U) to  G(K) for U containing K -/
@[simps]
def CoconeAFtoGι : FU K F P ⟶ (Functor.const _ ).obj (G.obj (op K))  where
  app W := σ.app _ ≫ limit.π (GK _ _) (op ⟨K, W.unop.property.1⟩)

/-- The cocone induced by the natural transformation CoconeAFtoG_NT-/
@[simps]
def CoconeAFtoG : Cocone (FU K F P) := Cocone.mk _ (CoconeAFtoGι σ K)

/-- The natural transformation  from α^* F to G induced taking the natural map from the limit to CoconeAFtoG-/
@[simps]
def AFtoG : ( (AlphaUpStar).obj F ⟶  G) where
  app K := colimit.desc _ (CoconeAFtoG _ K.unop)
  naturality _ _ f := by
    apply colimit.hom_ext
    intro _
    suffices _ = σ.app _ ≫ limit.π (GK _ _ ) (op _ ) ≫ G.map _ by simpa
    forceLimW
    · constructor
      exact f.unop
    · rfl

/-- The bijection between hom(αF, G) and hom(F,αG) -/
@[simps]
def homEquiv: (AlphaUpStar.obj F ⟶ G) ≃ ( F ⟶ AlphaDownStar.obj G) where
  toFun := fun τ => FtoAG τ
  invFun := fun σ  => AFtoG σ
  left_inv τ := by aesop_cat
  right_inv σ := by aesop_cat


/-- The data necessary to build the adjunction between α^* and α_*-/
@[simps]
def adjthm : Adjunction.CoreHomEquiv (AlphaUpStar) (@AlphaDownStar X _ C _ _) where
homEquiv := (@homEquiv _ _ _ _ _ _)
homEquiv_naturality_left_symm _ _ := by
  ext
  apply colimit.hom_ext
  simp [homEquiv]
homEquiv_naturality_right _ _ := by
  ext
  apply limit.hom_ext
  simp [homEquiv]

/-- The adjunction between α^* and α_*-/
@[simps!]
def AdjAlphaStar : (AlphaUpStar ) ⊣ (@AlphaDownStar X _ C _ _ ) := Adjunction.mkOfHomEquiv (adjthm)

--#lint
