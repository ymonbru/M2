
import M2.Ksheaves
import Mathlib.Topology.Sets.Opens

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite

variable {X} [TopologicalSpace X]
variable {C} [Category C] [HasColimits C] [HasLimits C]

attribute [local aesop safe (rule_sets := [CategoryTheory])] colimit.hom_ext limit.hom_ext

--α^*
noncomputable section
variable (K : Compacts X)
variable (F : (Opens X)ᵒᵖ ⥤ C)
variable (P : Opens X → Prop)-- true for the  le alpha normal et IsCompact (closure U.carrier) pour la version relativement compacte

/--The property of containing K and satisfying P-/
def KsubU : Set (Opens X) := fun (U:Opens _) => (K.carrier ⊆ U) ∧ P U

/--The full subcategory induced by the property KsubU-/
def KsubU_cat : Type := FullSubcategory (KsubU K P)

/-instance : SetLike (KsubU_cat K P) X where
  coe U:= U.obj.carrier

  coe_injective':= fun ⟨_ , _ ⟩ ⟨_, _⟩ h => by
    apply FullSubcategory.ext
    simp at h
    exact h-/


instance : Category (KsubU_cat K P) := FullSubcategory.category (KsubU K P)

/-- The diagram obtained by restricting F to the category KsubU-/
@[simps!]
def FU : (KsubU_cat K P)ᵒᵖ ⥤ C := Functor.comp (fullSubcategoryInclusion (KsubU K P)).op  F

variable (K₁ K₂ : Compacts X) (f : K₁ ⟶ K₂) --K1 ⊆ K2

/-- The functor that sends opens that containt K2 to opens that contains K1-/
@[simps]
def K1subK2subU : (KsubU_cat K₂ P) ⥤ (KsubU_cat K₁ P ) where
  obj W := (⟨W.obj,Set.Subset.trans (leOfHom _ ) W.property.1 , W.property.2⟩ : KsubU_cat _ _)
  map  _ := homOfLE (leOfHom _)

/-- The natural transformation of change of basis for the diagram FU-/
@[simps]
def K1subK2natTrans : (FU _ F P) ⟶  (Functor.comp (K1subK2subU _ _ _ f).op (FU _ F _)) where
  app _ := 𝟙 _

/-- The functor α^*F-/
@[simps]
def AlphaUpStarF : (Compacts X)ᵒᵖ ⥤ C  where
  obj K := colimit (FU K.unop F P)
  map f := colimMap (K1subK2natTrans F P _ _ f.unop) ≫ (colimit.pre (FU _ _ _) (K1subK2subU _ _ _ _ ).op)

variable (F₁ F₂ : (Opens X)ᵒᵖ ⥤ C) (τ : F₁ ⟶ F₂)

/-- The restriction of the natural transformation between the digram FU over K₁ eand FU over K₂ -/
@[simps]
def τres : (FU K F₁ P) ⟶ (FU _ F₂ _) where
  app U := τ.app <| op (U.unop.obj)

/-- The natural transformation α^* τ between α^* F₁ and α^* F₂-/
@[simps]
def AlphaUpStarTau : (AlphaUpStarF F₁ P) ⟶ (AlphaUpStarF F₂ P) where
  app K := colimMap (τres K.unop P _ _ τ)

/-- The functor α^* with the conditon P-/
@[simps]
def AlphaUpStarP : ((Opens X)ᵒᵖ ⥤ C) ⥤ (Compacts X)ᵒᵖ ⥤ C where
  obj _ := AlphaUpStarF _ _
  map := AlphaUpStarTau P _ _


/-- The condition that is always true -/
def trueCond :Opens X → Prop:= λ _ => true

/-- The first version of α^* -/
@[simps!]
def AlphaUpStar : ((Opens X)ᵒᵖ ⥤ C)⥤ ((Compacts X)ᵒᵖ ⥤ C) := AlphaUpStarP (trueCond)

end

noncomputable section
--α_*

variable (U : Opens X) (G : (Compacts X)ᵒᵖ ⥤ C)

/-- The condition over compacts subset of being contained in U -/
def UsupK : Set (Compacts X) := fun (K:Compacts X) => (K : Set X) ⊆ U

/-- The category induced by UsupK -/
def UsupK_cat : Type := FullSubcategory (UsupK U)

instance : Category (UsupK_cat U) := FullSubcategory.category (UsupK U)

/-- The diagrom obtained by restricting G to the subcategory UsupK-/
@[simps!]
def GK : (UsupK_cat U)ᵒᵖ ⥤ C := Functor.comp (fullSubcategoryInclusion (UsupK U)).op  G

variable (U₁ U₂ : Opens X) (f : U₁ ⟶ U₂)-- U₁ ⊆ U₂

/-- The functor that sends compacts contained  in U₁ to compaccts contained in U₂-/
@[simps]
def U2supU1supK : (UsupK_cat U₁) ⥤ (UsupK_cat U₂) where
  obj W := (⟨W.obj,Set.Subset.trans W.property (leOfHom f)⟩ : UsupK_cat _)
  map _ := homOfLE (leOfHom _)

/-- The natural transformation of change of basis for the diagram GK-/
@[simps]
def U2supU1natTrans : (GK _ G) ⟶  Functor.comp (U2supU1supK _ _ f).op (GK _ G) where
  app _ := 𝟙 _

variable [HasLimits C]

/-- The functor α_* G-/
@[simps]
def AlphaDownStarG : (Opens X)ᵒᵖ ⥤ C  where
  obj U := limit (GK U.unop G)
  map f := (limit.pre (GK _ G) (U2supU1supK _ _ f.unop).op) ≫ limMap (U2supU1natTrans G _ _ f.unop)

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
  obj _:= AlphaDownStarG _
  map := AlphaDownStarSigma _ _

end

--Adjunction

noncomputable section

variable {F : (Opens X)ᵒᵖ⥤ C} {G : (Compacts X)ᵒᵖ ⥤ C} (τ : (AlphaUpStar).obj F ⟶ G) (σ : F⟶ (AlphaDownStar).obj G) (K : Compacts X) (U : Opens X)


/-- The naturals maps from F(U) to the family of G(K) for K contained in U-/
@[simps]
def ConeFtoAG_NT : (Functor.const _ ).obj (F.obj (op U)) ⟶ GK U G where
  app L := colimit.ι (FU (fullSubcategoryInclusion _ |>.op.obj _ ).unop _ <| trueCond) (op ⟨U,L.unop.property,rfl⟩) ≫ τ.app _

  naturality _ L _ := by
    suffices _ = colimit.ι (FU _ _ _ ) (op ⟨U , _ ⟩) ≫ τ.app (op _ ) ≫ G.map _ by simpa
    rw [← (τ.naturality _)]
    simp [AlphaUpStar, K1subK2subU]

/-- The cone of the diragram GK U with point F(U)-/
@[simps]
def ConeFtoAG : Cone (GK U G) := Cone.mk _ (ConeFtoAG_NT τ _)

/-- The natural transformation from F to α_*G induced taking the natural map from ConeFtoAG to the colimit-/
@[simps]
def FtoAG : F ⟶ (AlphaDownStar).obj G where
  app U:= limit.lift _ (ConeFtoAG τ U.unop)
  naturality U V _ := by
    --ext ne trouve pas limit.hom_ext
    apply limit.hom_ext
    intro _
    suffices (FU _ _ _ ).map _ ≫ colimit.ι (FU _ _ _ ) (op ⟨V.unop, _ ⟩) ≫ _ = colimit.ι (FU _ _ _ ) (op ⟨U.unop, _ ⟩) ≫ _ by simpa
    rw [← Category.assoc, ← colimit.w_assoc, Category.assoc]


/-- The naturals maps from the family of F(U) to  G(K) for U containing K -/
@[simps]
def CoconeAFtoG_NT : FU K F P ⟶ (Functor.const _ ).obj (G.obj (op K))  where
  app W := σ.app _ ≫ limit.π (GK _ _) (op ⟨K, W.unop.property.1⟩)
  naturality _ _ _:= by
    suffices _ = σ.app _ ≫ limit.π (GK _ _) (op ⟨_,_⟩) by simpa
    rfl

/-- The cocone induced by the natural transformation CoconeAFtoG_NT-/
@[simps]
def CoconeAFtoG : Cocone (FU K F P) := Cocone.mk _ (CoconeAFtoG_NT σ K)

/-- The natural transformation  from α^* F to G induced taking the natural map from the limit to CoconeAFtoG-/
@[simps]
def AFtoG : ( (AlphaUpStar).obj F ⟶  G) where
  app K := colimit.desc _ (CoconeAFtoG _ K.unop)
  naturality _ _ _ := by
    apply colimit.hom_ext
    intro _
    suffices _ = σ.app _ ≫ limit.π (GK _ _ ) (op _ ) ≫ G.map _ by simpa [AlphaUpStar]
    rw [← limit.w _ _ ]
    rfl

/-- The bijection between hom(αF, G) and hom(F,αG) -/
--@[simps!] --#lint does not like it
def homEquiv: (AlphaUpStar.obj F ⟶ G) ≃ ( F ⟶ AlphaDownStar.obj G) where
  toFun := fun τ => FtoAG τ
  invFun := fun σ  => AFtoG σ
  left_inv τ := by aesop_cat
  right_inv σ := by aesop_cat


/-- The data necessary to build the adjunction between α^* and α_*-/
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
def AdjAlphaStar : (AlphaUpStar ) ⊣ (@AlphaDownStar X _ C _ _ ) := Adjunction.mkOfHomEquiv (adjthm)

--#lint
