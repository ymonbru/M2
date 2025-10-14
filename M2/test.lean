import M2.LimOfColimEx
import M2.colimOfColimEqColim
import M2.Suffices
import M2.RCalpha

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite TopCat TopCat.Presheaf
open ZeroObject

universe u v w z

variable {X : Type w} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
variable {C : Type u} [Category.{v, u} C] [HasLimitsOfSize.{w,w} C] [HasColimitsOfSize.{w,w} C]

variable (G : Ksheaf X C) (F : Sheaf C (of X)) (K K1 K2 : Compacts X) (P :Opens X → Prop)

noncomputable section

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
  carrier:= (AlphaUpStarP P).obj F.val
  ksh1 := by
    have : IsTerminal ((F.val).obj (op (⊥ : Opens X))) := by
      apply Sheaf.isTerminalOfBotCover F (⊥ : Opens X)
      intro _ hx
      rcases hx
    apply IsTerminal.ofIso this
    simp

    #check @asIso _ _ _ _ _ (isIso_ι_of_isTerminal (IsTerminalKsubUOpBotOp) (FU ⊥ F.val P))
  ksh2 K1 K2 := by
    apply Limits.IsLimit.ofIsoLimit _ (SquareSuptoInfIsColimLim F K1 K2)
    apply IsLimit.ofPreservesConeTerminal
    exact IsLimitConeOfColimF (limFUInterWCFlip F.val K1 K2) (colimFUInterWC F.val K1 K2) _ (limColimFUCap K1 K2 F) (limFUInterWCFlipLim K1 K2 F) (colimFUInterWCColim F.val K1 K2) _ (limColimFUCapIsLim K1 K2 F)
  ksh3 K := by
    apply Limits.IsColimit.ofIsoColimit _ (FLToKIsoToColimColim _ ).symm
    apply IsColimit.ofPreservesCoconeInitial
    apply colimIsColimColim _ _ (repOEx K) (repHEx K) (repLiftingEx K) _
    exact colimit.isColimit (FcupIaEx K F.val)

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
