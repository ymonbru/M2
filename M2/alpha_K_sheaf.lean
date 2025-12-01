import M2.forceLimW
import M2.LimOfColimEx
import M2.colimOfColimEqColim
import M2.Suffices
import M2.RCalpha
import M2.KsheafIso
import Mathlib.Topology.Sheaves.Stalks

import Mathlib

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite TopCat TopCat.Presheaf
open ZeroObject

universe u v w z

variable (X : Type w) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
variable (C : Type u) [Category.{v, u} C] [HasLimitsOfSize.{w,w} C] [HasColimitsOfSize.{w,w} C]

variable (G : Ksheaf X C) (F : Sheaf C (of X)) (K K1 K2 : Compacts X)

noncomputable section

/-variable (i : Type w) (U : i → Opens X ) (s : Cone ((Pairwise.diagram U).op ⋙ AlphaDownStarG G.carrier))

def trucπ : (Functor.const (UsupK_cat (iSup U))ᵒᵖ).obj s.pt ⟶ GK (iSup U) G.carrier where
  app K := by
    dsimp
    let h := s.π.app
    dsimp at h
    #check colimit.ι
    sorry

def truc : Cone (GK (iSup U) G.carrier) where
  pt := s.pt
  π := by

    sorry-/


/-- The evidence that α_* G is a sheaf-/
theorem KshToSh: IsSheaf (AlphaDownStarG G.carrier : Presheaf C (of X)):= by
  --probablement mieux d'utiliser isSheaf_iff_isSheafPairwiseIntersections
  apply (isSheaf_iff_isSheafPairwiseIntersections _).2
  unfold IsSheafPairwiseIntersections
  intro i U
  apply Nonempty.intro
  constructor
  · intro s j
    sorry
  · intro s m hm
    sorry
  · intro s
    simp
    have h := s.π.app
    dsimp at h

    #check limit.lift
    sorry

/-- α_* G as a sheaf-/
@[simps]
def shAlphaDownStarF : Sheaf C (of X) where
  val:= (AlphaDownStar).obj (G.carrier)
  cond := (KshToSh X C G)

/-- The functor α_* reistricted to Ksheaves and coreistricted to sheaves-/
@[simps]
def shAlphaDownStar : (Ksheaf X C) ⥤ Sheaf C (of X) where
  obj _ := shAlphaDownStarF X C _
  map f := Sheaf.Hom.mk ((AlphaDownStar).map f)
  map_id _ := by
    apply Sheaf.Hom.ext
    apply (AlphaDownStar).map_id
  map_comp _ _:= by
    apply Sheaf.Hom.ext
    apply (AlphaDownStar).map_comp

variable {X} {C}

/-- an isomorphism that represent FressSSK (used in ksh3 of ...) as a functor of the form colimFia-/
@[simps]
def AlphaUpFIsoColimFSubU : (FresSSK K (AlphaUpStar.obj F.val)) ≅ colimFia  (iaSubCEx K) (FcupIaEx K F.val) where
  hom := ⟨fun _ => colimMap (eqToHom rfl),fun _ _ _ => by
    apply colimit.hom_ext
    intro
    simp [_root_.F]⟩
  inv := ⟨fun _ => colimMap (eqToHom rfl),fun _ _ _ => by
    apply colimit.hom_ext
    intro
    simp [_root_.F]⟩

/-- The isomorphisme between the cocone that appear in ksh3 and the one that is in the generic theorem over colimits of colimits (transported through the isomorphism AlphaUpFIsoColimFSubU )-/
@[simps]
def FLToKIsoToColimColim {K :Compacts X} : (FLToFK K (AlphaUpStar.obj (F.val))) ≅ (Cocones.precomposeEquivalence (AlphaUpFIsoColimFSubU _ _ )).functor.obj (fCupIaCoconeToColimFiaCocone _ _ (colimit.cocone (FcupIaEx K F.val))) where
  hom := ⟨𝟙 (colimit (FU K F.val )), by aesop⟩
  inv := ⟨𝟙 (colimit (FcupIaEx K F.val)), by aesop⟩

/-- The isomorphism betwen the functor colimFUInterWCPt and colimit_{K1 ⊆ U}F(U) → colimit_{K1 ∩ K2 ⊆ U}F(U) ← colimit_{K2 ⊆ U} F(U)-/
@[simps!]
def colimFUInterWCIsoTwoVersion : (colimFUInterWC F.val K1 K2).pt ≅ cospan (FtoFInfLeft (AlphaUpStar.obj F.val) K1 K2) (FtoFInfRight (AlphaUpStar.obj F.val) K1 K2) := by
  refine IsoWcspFunc _ _ ?_ ?_ ?_ ?_ ?_
  · exact HasColimit.isoOfNatIso (jCompFEqProjCompFULeft F.val K1 K2) ≪≫ Functor.Final.colimitIso (KsubUK1K2ProjLeft K1 K2).op (FU K1 F.val)
  · exact HasColimit.isoOfNatIso (jCompFEqProjCompFURight F.val K1 K2) ≪≫ Functor.Final.colimitIso (KsubUK1K2ProjRight K1 K2).op (FU K2 F.val)
  · exact HasColimit.isoOfNatIso (jCompFEqProjCompFUOne F.val K1 K2) ≪≫ Functor.Final.colimitIso (subK1SubK2toSubK1InterK2 K1 K2).op (FU (K1 ⊓ K2) F.val)
  · apply colimit.hom_ext
    intro U
    suffices _ ≫ colimit.ι (FU (K1 ⊓ K2) F.val) (op ((subK1SubK2toSubK1InterK2 K1 K2).obj (unop U))) = colimit.ι (FU (K1 ⊓ K2) F.val) (op ((K1subK2subU _ (opHomOfLE _).unop).obj (unop U).1)) by simpa [FtoFInfLeft]
    forceColimW

  · apply colimit.hom_ext
    intro U
    suffices F.val.map ((jRToJO K1 K2).app U) ≫ colimit.ι (FU (K1 ⊓ K2) F.val) (op ((subK1SubK2toSubK1InterK2 K1 K2).obj (unop U))) = colimit.ι (FU (K1 ⊓ K2) F.val) (op ((K1subK2subU trueCond (opHomOfLE (by simp)).unop).obj (unop U).2)) by simpa [FtoFInfRight]
    forceColimW

/-- The inverse morphism of SquareSuptoInfIsColimLim-/
@[simps]
def SquareSuptoInfIsColimLimInv : (SquareSuptoInf (AlphaUpStar.obj F.val) K1 K2) ⟶ (Cones.postcomposeEquivalence (colimFUInterWCIsoTwoVersion F K1 K2)).functor.obj (ConeOverColimLimF (limFUInterWCFlip F.val K1 K2) (colimFUInterWC F.val K1 K2) (colimLimFUInterWCFlip K1 K2 F) (colimLimFUInterWCFlipIsColim K1 K2 F)) where
  hom := (HasColimit.isoOfNatIso (jCompFEqProjCompFUCup F.val K1 K2) ≪≫  Functor.Final.colimitIso (KsubUK1K2ProjCup K1 K2).op (FU (K1 ⊔ K2) F.val)).inv
  w x:= by
    suffices ((Cones.postcomposeEquivalence (colimFUInterWCIsoTwoVersion F K1 K2)).functor.obj (ConeOverColimLimF (limFUInterWCFlip F.val K1 K2) (colimFUInterWC F.val K1 K2)  (colimLimFUInterWCFlip K1 K2 F) (colimLimFUInterWCFlipIsColim K1 K2 F))).π.app x = (HasColimit.isoOfNatIso (jCompFEqProjCompFUCup F.val K1 K2) ≪≫ Functor.Final.colimitIso (KsubUK1K2ProjCup K1 K2).op (FU (K1 ⊔ K2) F.val)).hom ≫(SquareSuptoInf (AlphaUpStar.obj F.val) K1 K2).π.app x by
      rw[this]
      simp
    apply colimit.hom_ext
    intro U
    match x with
      | .left =>
        suffices F.val.map (op (homOfLE _)) ≫ colimit.ι (FU K1 F.val) (op (unop U).1) = colimit.ι (FU K1 F.val) (op ((K1subK2subU _ (opHomOfLE _).unop).obj ((KsubUK1K2ProjCup K1 K2).obj (unop U)))) by simpa [FSuptoFLeft, colimLimFUInterWCFlipIsColim]

        forceColimW
      | .right =>
        suffices F.val.map (op (homOfLE _)) ≫ colimit.ι (FU K2 F.val ) (op (unop U).2) = colimit.ι (FU K2 F.val) (op ((K1subK2subU _ (opHomOfLE _).unop).obj ((KsubUK1K2ProjCup K1 K2).obj (unop U)))) by simpa [FSuptoFRight, colimLimFUInterWCFlipIsColim]

        forceColimW
      | .one =>
        suffices F.val.map (op (homOfLE _)) ≫ colimit.ι (FU (K1 ⊓ K2) F.val) (op ((subK1SubK2toSubK1InterK2 K1 K2).obj (unop U))) = colimit.ι (FU (K1 ⊓ K2) F.val) (op ((K1subK2subU _ (opHomOfLE _).unop).obj ((K1subK2subU _ (opHomOfLE _).unop).obj ((KsubUK1K2ProjCup K1 K2).obj (unop U))))) by simpa [FSuptoFLeft, FtoFInfLeft, colimLimFUInterWCFlipIsColim]

        forceColimW

/-- The morphism of SquareSuptoInfIsColimLim-/
@[simps]
def SquareSuptoInfIsColimLimHom : (Cones.postcomposeEquivalence (colimFUInterWCIsoTwoVersion F K1 K2)).functor.obj (ConeOverColimLimF (limFUInterWCFlip F.val K1 K2) (colimFUInterWC F.val K1 K2) (colimLimFUInterWCFlip K1 K2 F) (colimLimFUInterWCFlipIsColim K1 K2 F)) ⟶ (SquareSuptoInf (AlphaUpStar.obj F.val) K1 K2) where
  hom := (HasColimit.isoOfNatIso (jCompFEqProjCompFUCup F.val K1 K2) ≪≫  Functor.Final.colimitIso (KsubUK1K2ProjCup K1 K2).op (FU (K1 ⊔ K2) F.val)).hom
  w := by
    intro
    rw [← (SquareSuptoInfIsColimLimInv F K1 K2).w _]
    simp

/-- The isomorphisme between the cocone that appear in ksh2 and the one that is in the generic theorem over limits of colimits (transported through the isomorphism colimFUInterWCIsoTwoVersion )-/
@[simps]
def SquareSuptoInfIsColimLim: (Cones.postcomposeEquivalence (colimFUInterWCIsoTwoVersion F K1 K2)).functor.obj (ConeOverColimLimF (limFUInterWCFlip F.val K1 K2) (colimFUInterWC F.val K1 K2) (colimLimFUInterWCFlip K1 K2 F) (colimLimFUInterWCFlipIsColim K1 K2 F)) ≅ (SquareSuptoInf (AlphaUpStar.obj F.val) K1 K2) where
  hom := SquareSuptoInfIsColimLimHom F K1 K2
  inv := SquareSuptoInfIsColimLimInv F K1 K2

variable (X) (C)
variable [HasForget C]  [(forget C).ReflectsIsomorphisms] [HasFiniteLimits C] [∀ (K1 K2 : Compacts X), PreservesColimitsOfShape (KsubU_cat K1 × KsubU_cat K2)ᵒᵖ (forget C)] [PreservesFiniteLimits (forget C)] [∀ (K1 K2 : Compacts X), Small.{v, w} (KsubU_cat K1 × KsubU_cat K2)ᵒᵖ]
-- True for example if C = Type w
-- It's for a^* F to be a K-sheaf

/-- The structur of Ksheaf over (AlphaUpStar).obj F-/
@[simps!]
def shAlphaUpStarG : (Ksheaf X C) where
  carrier:= (AlphaUpStar).obj F.val
  ksh1 := by
    have : IsTerminal ((F.val).obj (op (⊥ : Opens X))) := by
      apply Sheaf.isTerminalOfBotCover F (⊥ : Opens X)
      intro _ hx
      rcases hx
    apply IsTerminal.ofIso this
    apply @asIso _ _ _ _ _ (isIso_ι_of_isTerminal (IsTerminalKsubUOpBotOpTrue) (FU ⊥ F.val ))
  ksh2 K1 K2 := by
    apply Limits.IsLimit.ofIsoLimit _ (SquareSuptoInfIsColimLim F K1 K2)
    apply IsLimit.ofPreservesConeTerminal
    exact IsLimitConeOfColimF (limFUInterWCFlip F.val K1 K2) (colimFUInterWC F.val K1 K2) _ (limColimFUCap K1 K2 F) (limFUInterWCFlipLim K1 K2 F) (colimFUInterWCColim F.val K1 K2) _ (limColimFUCapIsLim K1 K2 F)
  ksh3 K := by
    apply Limits.IsColimit.ofIsoColimit _ (FLToKIsoToColimColim _ ).symm
    apply IsColimit.ofPreservesCoconeInitial
    apply colimIsColimColim _ _ (repOEx K) (repHEx K) (repLiftingEx K) _
    exact colimit.isColimit (FcupIaEx K F.val)

/-- The structur of Ksheaf over (AlphaUpStarRc).obj F-/
@[simps!]
def shAlphaUpStarRcG : (Ksheaf X C) := KsheafOfIso (AlphaUpStarRc.obj F.val) (shAlphaUpStarG X C F) ((AlphaUpStarToRc C X).app F.val)

/-- α^* as a functor restricted to sheaves and corestricted to Ksheaves-/
@[simps]
def shAlphaUpStar : Sheaf C (of X) ⥤ (Ksheaf X C) where
  obj G := shAlphaUpStarG X C G
  map f := (AlphaUpStar).map ((Sheaf.forget _ _).map f)
  map_id G := by
    -- j'ai remplace Sheaf.forget F par F.val pour simplifier et du coup il ne sait plus faire ça
    have : 𝟙 ((Sheaf.forget C (of X)).obj G) = 𝟙 G.val := by rfl
    rw [(Sheaf.forget C (of X)).map_id, this, AlphaUpStar.map_id]
    rfl

@[simps]
def shAlphaUpStarRc : Sheaf C (of X) ⥤ (Ksheaf X C) where
  obj G := shAlphaUpStarRcG X C G
  map f := (AlphaUpStarRc).map ((Sheaf.forget _ _).map f)
  map_id G := by
    -- j'ai remplace Sheaf.forget F par F.val pour simplifier et du coup il ne sait plus faire ça
    have : 𝟙 ((Sheaf.forget C (of X)).obj G) = 𝟙 G.val := by rfl
    rw [(Sheaf.forget C (of X)).map_id, this, AlphaUpStarRc.map_id]
    rfl

--Restrict the adjunction

/-- The adjunction between α^* and α_* restricted to sheaves and Ksheaves-/
def AdjShAlphaStar : (shAlphaUpStar X C ) ⊣ (shAlphaDownStar X C) := by
  apply (Adjunction.restrictFullyFaithful  (@AdjAlphaStar X _ C _ _ _) _ _) _ _

  apply Sheaf.forget
  apply (inducedFunctor (fun (F:Ksheaf X C) => F.carrier))
  apply @Functor.FullyFaithful.ofFullyFaithful _ _ _ _ _ (Sheaf.forget_full _ _) (Sheaf.forgetFaithful _ _)

  apply fullyFaithfulInducedFunctor
  exact ⟨𝟙 _,𝟙 _,by aesop_cat,by aesop_cat⟩
  exact ⟨𝟙 _,𝟙 _,by aesop_cat,by aesop_cat⟩

/-- The adjunction between α^*RC and α_* restricted to sheaves and Ksheaves-/
def AdjShAlphaStarRc : (shAlphaUpStarRc X C ) ⊣ (shAlphaDownStar X C) := by
  --exact (AdjShAlphaStar X C).ofNatIsoLeft (AlphaShUpStarToRc X C).symm
  apply (Adjunction.restrictFullyFaithful  (AdjAlphaStarRc C X) _ _) _ _

  apply Sheaf.forget
  apply (inducedFunctor (fun (F:Ksheaf X C) => F.carrier))
  apply @Functor.FullyFaithful.ofFullyFaithful _ _ _ _ _ (Sheaf.forget_full _ _) (Sheaf.forgetFaithful _ _)

  apply fullyFaithfulInducedFunctor
  exact ⟨𝟙 _,𝟙 _,by aesop_cat,by aesop_cat⟩
  exact ⟨𝟙 _,𝟙 _,by aesop_cat,by aesop_cat⟩



--end
--noncomputable section
--adjonction donne une équivalence de catégorie



--variable  [ConcreteCategory C] [(forget C).ReflectsIsomorphisms ] [PreservesLimits (forget C)] [PreservesFilteredColimits (forget C)]
--variable [HasColimits C]
/- sur d'avoir besoin de tout ça?, en tout cas pour stalk iso functeur oui-/

-- il semble que utiliser le fait que deux faiseaux soient isomorphes ssi ils le sont sur les stalks ajoute encore des hyp sur C donc on va essayer sans
#check TopCat.Presheaf.isIso_of_stalkFunctor_map_iso
variable (G : Ksheaf X C) (F : Sheaf C (of X)) -- in order to get the variable in the right place for next theorems
variable {X} {C}

variable (U : Opens X)



/-def infInfU : Set (Opens X) := fun (V  : Opens _ )=> (∃ L: Compacts _ , V.carrier ⊆ L.carrier ∧ L.carrier ⊆ U.carrier )

def infInfU_cat : Type w := ObjectProperty.FullSubcategory (infInfU U)

instance : Category (infInfU_cat U ) := ObjectProperty.FullSubcategory.category (infInfU U)

def FresIIU : (infInfU_cat U)ᵒᵖ ⥤ C := (ObjectProperty.ι (infInfU U)).op.comp F.val-/

@[simps]
def intFunc : UsupK_cat U ⥤ Opens X where
obj K := ⟨ interior K.obj.carrier, isOpen_interior⟩
map {K L} f := homOfLE <| interior_mono <| leOfHom f

@[simps!]
def Fcirc : (UsupK_cat U)ᵒᵖ ⥤ C := (intFunc U).op.comp F.val

@[simps]
def trucπ : (Functor.const (UsupK_cat U)ᵒᵖ).obj (F.val.obj (op U)) ⟶ Fcirc F U where
  app K := F.val.map <| op <| homOfLE <| by apply subset_trans (interior_mono K.unop.property) (interior_subset)
  naturality { K L} f := by
    simp
    rw [← F.val.map_comp]
    rfl

def machin : (UsupK_cat U) → Opens (of X) := fun K => (intFunc U).obj K


#check Classical.choice (TopCat.Presheaf.IsSheaf.isSheafOpensLeCover (F := F.val) (machin U) (by sorry))


--@[simps]
def truc : Cone (Fcirc F U) where
  pt := F.val.obj (op U)
  π := trucπ F U

def trucLimit: IsLimit (truc F U) where
  lift s := by
    dsimp [truc]
    #check s.π.app
    sorry


variable (U : (Opens X)ᵒᵖ )
/-variable (U : (Opens X)ᵒᵖ ) (L : (UsupK_cat (unop U))ᵒᵖ)

def biduleι :FU (unop L).obj F.val ⟶ (Functor.const (KsubU_cat (unop L).obj)ᵒᵖ).obj (F.val.obj U) where
  app V := by
    apply F.val.map
    apply op
    apply homOfLE
    simp
    -- un tel L n'existe pas même dans R....
    sorry

def bidule : Cocone (FU (unop L).obj F.val) where
  pt  := F.val.obj U
  ι := biduleι F U L-/

@[simps]
def truc3π : (Functor.const (UsupK_cat (unop U))ᵒᵖ).obj (((AlphaUpStar ⋙ AlphaDownStar).obj F.val).obj U) ⟶ GK (unop U) (AlphaUpStar.obj F.val) where
  app K := limit.π _ K
  naturality {K L} f:= by
    simp
    forceLimW

@[simps]
def truc3 : Cone  (GK U.unop (AlphaUpStar.obj F.val) ) where
  pt := ((AlphaUpStar ⋙ AlphaDownStar ).obj F.val).obj U
  π := truc3π F U

variable (K : (UsupK_cat (unop U))ᵒᵖ)

@[simps]
def biduleCoconeι : FU (unop K).obj F.val ⟶ (Functor.const (KsubU_cat (unop K).obj)ᵒᵖ).obj (F.val.obj (op ((intFunc (unop U)).obj (unop K)))) where
  app V := F.val.map <| op <| homOfLE <| by apply subset_trans (interior_mono V.unop.property.1) (interior_subset)
  naturality { V W} f := by
    simp
    rw [← F.val.map_comp]
    rfl

@[simps]
def biduleCocone : Cocone (FU (unop K).obj F.val) where
  pt := F.val.obj (op ((intFunc (unop U)).obj (unop K)))
  ι := biduleCoconeι F U K

@[simps]
def bidule : (GK (unop U) (AlphaUpStar.obj F.val) ⟶ Fcirc F (unop U)) where
  app K:= by
    apply colimit.desc _ (biduleCocone F U K)
  naturality {K L } f  := by
    apply colimit.hom_ext
    intro V
    simp
    rw [← F.val.map_comp]
    rfl


def UnitAlphaInv : ((AlphaUpStar ⋙ AlphaDownStar ).obj F.val).obj U  ⟶ F.val.obj U := (trucLimit F U.unop).map (truc3 F U) (bidule F U)

@[simps]
def truc2π : (Functor.const (UsupK_cat (unop U))ᵒᵖ).obj (F.val.obj U) ⟶ GK (unop U) (AlphaUpStar.obj F.val)  where
  app K := colimit.ι (FU (unop K).obj F.val) (op <| UsupKToKsubU (unop K))

@[simps]
def truc2 : Cone  (GK (unop U) (AlphaUpStar.obj F.val)) where
  pt := F.val.obj U
  π := truc2π F U

--def UnitAlphaAppApp : F.val.obj U ⟶ ((AlphaUpStar ⋙ AlphaDownStar ).obj F.val).obj U := (AdjAlphaStar.unit.app F.val).app U

omit [T2Space X] [LocallyCompactSpace X] [HasForget C] [(forget C).ReflectsIsomorphisms] [HasFiniteLimits C] [∀ (K1 K2 : Compacts X), PreservesColimitsOfShape (KsubU_cat K1 × KsubU_cat K2)ᵒᵖ (forget C)] [PreservesFiniteLimits (forget C)] [∀ (K1 K2 : Compacts X), Small.{v, w} (KsubU_cat K1 × KsubU_cat K2)ᵒᵖ] in
lemma machinEq : limit.lift _ (truc2 F U) = (AdjAlphaStar.unit.app F.val).app U := by
  apply limit.hom_ext
  intro K
  simp --[UnitAlphaAppApp]
  rfl

omit [HasForget C] [(forget C).ReflectsIsomorphisms] [HasFiniteLimits
  C] [∀ (K1 K2 : Compacts X), PreservesColimitsOfShape (KsubU_cat K1 × KsubU_cat K2)ᵒᵖ (forget C)] [PreservesFiniteLimits (forget C)] [∀ (K1 K2 : Compacts X), Small.{v, w} (KsubU_cat K1 × KsubU_cat K2)ᵒᵖ] in
theorem IsoAlphaUnit : IsIso (((AdjAlphaStar).unit.app F.val).app U) := by
  use UnitAlphaInv F U
  constructor
  · rw [← machinEq F U]
    suffices limit.lift (GK (unop U) (AlphaUpStar.obj F.val)) (truc2 F U) ≫ IsLimit.map (truc3 F U) (trucLimit F (unop U)) (bidule F U) = 𝟙 (F.val.obj U) by simpa [UnitAlphaInv]
    apply IsLimit.hom_ext (trucLimit F (unop U))
    intro K
    suffices F.val.map (op (homOfLE _)) = (truc F (unop U)).π.app K by simpa
    dsimp [truc]-- pourquoi diable si on met simps à truc il ne s'en sort pas
  · apply limit.hom_ext
    intro K
    --unfold UnitAlphaInv
    rw [← machinEq]

    suffices UnitAlphaInv F U ≫ colimit.ι (FU (unop K).obj F.val) (op (UsupKToKsubU (unop K))) = limit.π (GK (unop U) (AlphaUpStar.obj F.val)) K by simpa

    let L : (UsupK_cat (unop U))ᵒᵖ := by
      apply op
      let Lcirc := (Vloc X _ (UsupKToKsubU (unop K)))
      use (closureFunc _ ).obj Lcirc
      simp [UsupK]
      apply V_closure

    let KsubL : KsubU (unop K).obj trueCond ((intFunc (unop U)).obj (unop L)) := by
      simp only [KsubU, carrier_eq_coe, coe_intFunc_obj, coe_closureFunc_obj, trueCond, and_true, L]
      apply Set.Subset.trans _
      apply interior_mono
      apply subset_closure
      apply V_interior

    let f : (op (UsupKToKsubU (unop K))) ⟶ op ⟨((intFunc (unop U)).obj (unop L)), KsubL⟩ := by
      apply op
      apply homOfLE
      apply Set.Subset.trans
      apply interior_subset
      apply V_closure

    rw [← colimit.w _ f]

    have h := IsLimit.map_π (truc3 F U) (trucLimit F (unop U)) (bidule F U) L

    have : UnitAlphaInv F U ≫ (FU (unop K).obj F.val).map f  = (truc3 F U).π.app L ≫ (bidule F U).app L := by
      rw [← h]-- mais par contre on ne peut pas rw h directement dans ce qui suit
      rfl

    slice_lhs 1 2 => rw [this]

    simp
    forceLimW
    · apply Set.Subset.trans
      exact KsubL.1
      apply interior_subset
    · apply colimit.hom_ext
      intro V
      suffices F.val.map (op (homOfLE _)) ≫ colimit.ι (FU (unop K).obj F.val) (op { obj := (intFunc (unop U)).obj (unop L), property := KsubL }) = colimit.ι (FU (unop K).obj F.val) (op ((K1subK2subU trueCond fForce.unop).obj (unop V))) by simpa
      forceColimW

theorem IsoAlphaShUnit : IsIso ((AdjShAlphaStar X C).unit.app F):= by
  have : IsIso ((Sheaf.forget C (of X)).map ((AdjShAlphaStar X C).unit.app F)) := by
    unfold AdjShAlphaStar
    rw [CategoryTheory.Adjunction.map_restrictFullyFaithful_unit_app]
    apply ((CategoryTheory.NatTrans.isIso_iff_isIso_app) _).2
    intro U
    dsimp
    apply CategoryTheory.IsIso.comp_isIso'
    · exact IsoAlphaUnit F U
    · -- ça on ne devrait pas avoir à le faire
      use 𝟙 _
      constructor
      · suffices limMap _ =  𝟙 (limit (GK (unop U) (AlphaUpStar.obj ((Sheaf.forget C (of X)).obj F)))) by simpa [σres]
        ext
        simp
      · apply limit.hom_ext
        intro K
        simp
        rfl
  apply CategoryTheory.isIso_of_fully_faithful (Sheaf.forget C (of X))

variable (K : Compacts X) (G : Ksheaf X C) (F : Sheaf C (of X)) -- in order to get the variable in the right place for next theorems

variable  (U : RelCN_cat K)

@[simps]
def GUbarToAlphaDownStarGConeπ : (Functor.const (UsupK_cat U.obj)ᵒᵖ).obj ((FUbar K G.carrier).obj (op U)) ⟶ GK U.obj G.carrier where
  app K' := G.carrier.map <| op <| homOfLE<| by
     apply le_trans K'.unop.property subset_closure
  naturality _ _ f := by
    suffices G.carrier.map (op (homOfLE _)) = G.carrier.map (op (homOfLE _)) ≫ G.carrier.map _ by simpa
    rw [← G.carrier.map_comp]
    rfl

@[simps]
def GUbarToAlphaDownStarGCone : Cone (GK U.obj G.carrier) where
  pt := (FUbar K G.carrier).obj <| op U
  π := GUbarToAlphaDownStarGConeπ K G U

@[simps]
def GUbarToAlphaDownStarG : FUbar K G.carrier ⟶ FU K (AlphaDownStar.obj G.carrier) relcCond where
  app U := limit.lift _ (GUbarToAlphaDownStarGCone K G U.unop)
  naturality {U V} f:= by
    apply limit.hom_ext
    intro K'
    suffices G.carrier.map ((closureFunc K).map f.unop).op ≫ G.carrier.map (op (homOfLE _)) = G.carrier.map (op (homOfLE _)) by simpa
    rw [ ← G.carrier.map_comp]
    rfl

@[simps]
def CounitAlphaInvCoconeι : FU K (AlphaDownStar.obj G.carrier) relcCond ⟶
  (Functor.const (KsubU_cat K relcCond)ᵒᵖ).obj (((AlphaDownStar ⋙ AlphaUpStarRc).obj G.carrier).obj (op K)) where
    app U := colimit.ι _ U
    naturality { U V} f := by
      suffices limit.pre (GK (unop U).obj G.carrier) (U2supU1supK (unop V).obj (unop U).obj f.unop).op ≫ limMap (𝟙 ((U2supU1supK (unop V).obj (unop U).obj f.unop).op ⋙ GK (unop U).obj G.carrier)) ≫  colimit.ι (FU K (AlphaDownStarG G.carrier) relcCond) V = colimit.ι (FU K (AlphaDownStarG G.carrier) relcCond) U by simpa
      forceColimW

@[simps]
def CounitAlphaInvCocone : Cocone (FU K (AlphaDownStar.obj G.carrier) relcCond) where
  pt := ((AlphaDownStar ⋙ AlphaUpStarRc).obj G.carrier).obj (op K)
  ι := CounitAlphaInvCoconeι K G

def CounitAlphaInv : G.carrier.obj (op K) ⟶ ((AlphaDownStar ⋙ AlphaUpStarRc).obj G.carrier).obj (op K) := ((FUbarEquivFL K G.carrier).invFun (G.ksh3 K)).map (CounitAlphaInvCocone K G) (GUbarToAlphaDownStarG K G)

def CounitAlphaAppApp : ((AlphaDownStar ⋙ AlphaUpStarRc).obj G.carrier).obj (op K) ⟶ G.carrier.obj (op K) := ((AdjAlphaStarRc C X).counit.app G.carrier).app (op K)

def CounitAlphaV2Coconeι : FU K (AlphaDownStarG G.carrier) relcCond ⟶ (Functor.const (KsubU_cat K relcCond)ᵒᵖ).obj (G.carrier.obj (op K)) where
  app U := limit.π (GK (unop U).obj G.carrier) (op (KsubUToUsupK U.unop))

@[simps]
def CounitAlphaV2Cocone : Cocone (FU K (AlphaDownStarG G.carrier) relcCond) where
  pt := G.carrier.obj (op K)
  ι := CounitAlphaV2Coconeι K G

omit [HasForget C] [(forget C).ReflectsIsomorphisms] [HasFiniteLimits
  C] [∀ (K1 K2 : Compacts X), PreservesColimitsOfShape (KsubU_cat K1 × KsubU_cat K2)ᵒᵖ (forget C)] [PreservesFiniteLimits (forget C)] [∀ (K1 K2 : Compacts X), Small.{v, w} (KsubU_cat K1 × KsubU_cat K2)ᵒᵖ] in
lemma CounitAlphaEq : colimit.desc _ (CounitAlphaV2Cocone K G) = CounitAlphaAppApp K G := by
  apply colimit.hom_ext
  intro U
  simp [CounitAlphaAppApp]
    -- vraiment faire une tactique forcecolimit.ι_pre
  have : colimit.ι (FU K (AlphaDownStarG G.carrier) relcCond) U ≫
    colimit.pre (FU K (AlphaDownStarG G.carrier) fun x ↦ true = true) (KsubUPtoQ K (λ _ _ => rfl)).op = colimit.ι (FU K (AlphaDownStarG G.carrier) ) ((KsubUPtoQ K (λ _ _ => rfl)).op.obj U) := by
        exact colimit.ι_pre (FU K (AlphaDownStarG G.carrier) fun x ↦ true = true) (KsubUPtoQ K (λ _ _ => rfl)).op _
  slice_rhs 1 2 => rw [this]

  simp [AdjAlphaStar, homEquiv]
  rfl


omit [HasForget C] [(forget C).ReflectsIsomorphisms] [HasFiniteLimits
  C] [∀ (K1 K2 : Compacts X), PreservesColimitsOfShape (KsubU_cat K1 × KsubU_cat K2)ᵒᵖ (forget C)] [PreservesFiniteLimits (forget C)] [∀ (K1 K2 : Compacts X), Small.{v, w} (KsubU_cat K1 × KsubU_cat K2)ᵒᵖ] in
lemma CounitAlphaInvCompHomEqId : CounitAlphaInv K G ≫ CounitAlphaAppApp K G = 𝟙 _ := by
  apply IsColimit.hom_ext ((FUbarEquivFL K G.carrier).invFun (G.ksh3 K))
  intro U
  unfold CounitAlphaInv
  slice_lhs 1 2 => rw [IsColimit.ι_map]
  simp [CounitAlphaInvCocone, CounitAlphaInvCoconeι, CounitAlphaAppApp]

    -- vraiment faire une tactique forcecolimit.ι_pre
  have : colimit.ι (FU K (AlphaDownStarG G.carrier) relcCond) U ≫ colimit.pre (FU K (AlphaDownStarG G.carrier) fun x ↦ true = true) (KsubUPtoQ K (λ _ _ => rfl)).op = colimit.ι (FU K (AlphaDownStarG G.carrier) ) ((KsubUPtoQ K (λ _ _ => rfl)).op.obj U) := by
    exact colimit.ι_pre (FU K (AlphaDownStarG G.carrier) fun x ↦ true = true) (KsubUPtoQ K (λ _ _ => rfl)).op _

  slice_lhs 2 3 => rw [this]
  simp [AdjAlphaStar, homEquiv]


omit [HasForget C] [(forget C).ReflectsIsomorphisms] [HasFiniteLimits
  C] [∀ (K1 K2 : Compacts X), PreservesColimitsOfShape (KsubU_cat K1 × KsubU_cat K2)ᵒᵖ (forget C)] [PreservesFiniteLimits (forget C)] [∀ (K1 K2 : Compacts X), Small.{v, w} (KsubU_cat K1 × KsubU_cat K2)ᵒᵖ] in
-- but rendre ce lemme qui suit propre avec pleins de tactiques
lemma CounitAlphaHomCompInvEqId : CounitAlphaAppApp K G ≫ CounitAlphaInv K G = 𝟙 _ := by
  apply colimit.hom_ext
  intro U
  rw [← CounitAlphaEq]

  let V : (KsubU_cat K relcCond)ᵒᵖ := op <| Vloc X K ((KsubUPtoQ K (λ _ _ => rfl)).obj U.unop)
  let f : U ⟶ V := by
    apply op
    apply homOfLE
    apply V_spec

  suffices (CounitAlphaV2Coconeι K G).app U ≫ CounitAlphaInv K G = colimit.ι (FU K (AlphaDownStarG G.carrier) relcCond) U by simpa

  have : (FU K (AlphaDownStarG G.carrier) relcCond).map f ≫ (CounitAlphaV2Coconeι K G).app V = (CounitAlphaV2Coconeι K G).app U := by
    rw [ (CounitAlphaV2Coconeι K G).naturality f]
    simp
  rw [← this]
  suffices ((FU K (AlphaDownStarG G.carrier) relcCond).map f ≫ (CounitAlphaV2Coconeι K G).app V) ≫ ((FUbarEquivFL K G.carrier).invFun (G.ksh3 K)).map (CounitAlphaInvCocone K G) (GUbarToAlphaDownStarG K G) = colimit.ι (FU K (AlphaDownStarG G.carrier) relcCond) U by simpa only [CounitAlphaInv]

  have hVU : ((closureFunc K).obj V.unop).carrier ≤ U.unop.obj := by
    apply V_closure

  suffices limit.π (GK (unop U).obj G.carrier) (op ((U2supU1supK (unop V).obj (unop U).obj f.unop).obj (KsubUToUsupK (unop V)))) ≫ ((FUbarEquivFL K G.carrier).symm (G.ksh3 K)).map (CounitAlphaInvCocone K G) (GUbarToAlphaDownStarG K G) = colimit.ι (FU K (AlphaDownStarG G.carrier) relcCond) U by simpa [CounitAlphaV2Coconeι]

  let L : (UsupK_cat (unop U).obj)ᵒᵖ := ⟨((closureFunc K).op.obj V).unop, by
    simp [UsupK]
    exact hVU⟩

  have : limit.π (GK (unop U).obj G.carrier) (op ((U2supU1supK (unop V).obj (unop U).obj f.unop).obj (KsubUToUsupK (unop V)))) = limit.π (GK (unop U).obj G.carrier) L ≫ (FUbarToFK K G.carrier).ι.app V := by forceLimW

  rw [this]
  slice_lhs 2 3 => rw [IsColimit.ι_map]

  simp [CounitAlphaInvCocone, CounitAlphaInvCoconeι]
  forceColimW

  apply limit.hom_ext
  intro M
  suffices limit.π (GK (unop U).obj G.carrier) L ≫ G.carrier.map (op (homOfLE _)) =
  limit.π (GK (unop U).obj G.carrier) (op ((U2supU1supK (unop V).obj (unop U).obj fForce.unop).obj (unop M))) by simpa
  forceLimW

omit [HasForget C] [(forget C).ReflectsIsomorphisms] [HasFiniteLimits
  C] [∀ (K1 K2 : Compacts X), PreservesColimitsOfShape (KsubU_cat K1 × KsubU_cat K2)ᵒᵖ (forget C)] [PreservesFiniteLimits (forget C)] [∀ (K1 K2 : Compacts X), Small.{v, w} (KsubU_cat K1 × KsubU_cat K2)ᵒᵖ] in
theorem IsoAlphaCounit : IsIso (((AdjAlphaStarRc C X).counit.app G.carrier).app (op K)) := by
  use CounitAlphaInv K G
  constructor
  apply CounitAlphaHomCompInvEqId
  apply CounitAlphaInvCompHomEqId

theorem IsoAlphaRcShCoUnit : IsIso ((AdjShAlphaStarRc X C).counit.app G):= by

  have : IsIso ((KsheafToPre X C).map ((AdjShAlphaStarRc X C).counit.app G)) := by
    unfold AdjShAlphaStarRc
    rw [CategoryTheory.Adjunction.map_restrictFullyFaithful_counit_app]
    apply ((CategoryTheory.NatTrans.isIso_iff_isIso_app) _).2
    intro K
    suffices IsIso (colimit.pre (FU (unop K) (AlphaDownStarG G.carrier) fun x ↦ true = true) (KsubUPtoQ (unop K) _).op ≫
    ((AdjAlphaStar.homEquiv (AlphaDownStarG G.carrier) G.carrier).symm (𝟙 (AlphaDownStarG G.carrier))).app K) by simpa
    exact IsoAlphaCounit K.unop G
  apply CategoryTheory.isIso_of_fully_faithful (KsheafToPre X C)

theorem IsoAlphaShCoUnit : IsIso ((AdjShAlphaStar X C).counit.app G):= by
  let h := CategoryTheory.Adjunction.leftAdjointUniq (AdjShAlphaStar X C) (AdjShAlphaStarRc X C)

  let e : (Functor.whiskerLeft _ h.hom) ≫ (AdjShAlphaStarRc X C).counit = (AdjShAlphaStar X C).counit := by
    ext
    simp [h]
  rw [← e]
  suffices IsIso ((AdjShAlphaStarRc X C).counit.app G) by simpa
  exact IsoAlphaRcShCoUnit G

/-- The isomorphism between the category of sheaves and the category of Ksheaves-/
def KshIsoSh: (Sheaf C (of X)) ≌ (Ksheaf X C) := by
   apply @Adjunction.toEquivalence _ _ _ _  _  _ (AdjShAlphaStar X C) IsoAlphaShUnit IsoAlphaShCoUnit

example : (Sheaf (Type w) (of X)) ≌ (Ksheaf X (Type w)) := by
  apply KshIsoSh

example : (Sheaf Ab (of X)) ≌ (Ksheaf X Ab) := by
  apply KshIsoSh

--#min_imports
--#lint
