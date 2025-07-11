import M2.alpha
import M2.colimOfColimEqColim
import M2.LimOfColimEx
import M2.forceColimW
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.Sheaves.Sheaf
--import Mathlib.Topology.Sheaves.SheafCondition.OpensLeCover
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.Topology.Sheaves.Stalks
--import Mathlib.CategoryTheory.Limits.Fubini
--import Mathlib.CategoryTheory.Limits.Final
--import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite TopCat TopCat.Presheaf
open ZeroObject

universe u v w z

variable (X : Type w) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
variable (C : Type u) [Category.{v, u} C] [HasLimitsOfSize.{w,w} C] [HasColimitsOfSize.{w,w} C]

variable (G : Ksheaf X C) (F : Sheaf C (of X)) (K K1 K2 : Compacts X)

noncomputable section

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
    /-have f : (op ((K1subK2subU _ (opHomOfLE (FtoFInfLeft._proof_1 K1 K2)).unop).obj (unop U).1)) ⟶ (op ((subK1SubK2toSubK1InterK2 K1 K2).obj (unop U))) := by
      apply op
      apply homOfLE
      simp
    rw [← colimit.w _ f]; aesop_cat
    suffices F.val.map ((jLToJO K1 K2).app U) ≫
    colimit.ι (FU (K1 ⊓ K2) F.val) (op ((subK1SubK2toSubK1InterK2 K1 K2).obj (unop U))) = F.val.map f.unop.op ≫ colimit.ι (FU (K1 ⊓ K2) F.val) (op ((subK1SubK2toSubK1InterK2 K1 K2).obj (unop U))) by simpa
    rfl-/
  · apply colimit.hom_ext
    intro U
    --simp [FtoFInfRight]
    suffices F.val.map ((jRToJO K1 K2).app U) ≫ colimit.ι (FU (K1 ⊓ K2) F.val) (op ((subK1SubK2toSubK1InterK2 K1 K2).obj (unop U))) = colimit.ι (FU (K1 ⊓ K2) F.val) (op ((K1subK2subU trueCond (opHomOfLE (by simp)).unop).obj (unop U).2)) by simpa [FtoFInfRight]

    forceColimW
    /-have f : (op ((K1subK2subU _ (opHomOfLE (FtoFInfRight._proof_1 K1 K2)).unop).obj (unop U).2)) ⟶ (op ((subK1SubK2toSubK1InterK2 K1 K2).obj (unop U))) := by
      apply op
      apply homOfLE
      simp
    rw [← colimit.w _ f]
    suffices F.val.map ((jRToJO K1 K2).app U) ≫
    colimit.ι (FU (K1 ⊓ K2) F.val) (op ((subK1SubK2toSubK1InterK2 K1 K2).obj (unop U))) = F.val.map f.unop.op ≫ colimit.ι (FU (K1 ⊓ K2) F.val) (op ((subK1SubK2toSubK1InterK2 K1 K2).obj (unop U))) by simpa
    rfl-/

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
        /-have f : (op ((K1subK2subU _ (opHomOfLE (by simp)).unop).obj ((KsubUK1K2ProjCup K1 K2).obj (unop U)))) ⟶ (op (unop U).1) := by
          apply op
          apply homOfLE
          simp
        rw [← colimit.w _ f]
        simp
        rfl-/
      | .right =>
        suffices F.val.map (op (homOfLE _)) ≫ colimit.ι (FU K2 F.val ) (op (unop U).2) = colimit.ι (FU K2 F.val) (op ((K1subK2subU _ (opHomOfLE _).unop).obj ((KsubUK1K2ProjCup K1 K2).obj (unop U)))) by simpa [FSuptoFRight, colimLimFUInterWCFlipIsColim]

        forceColimW
        /-have f : (op ((K1subK2subU _ (opHomOfLE (by simp)).unop).obj ((KsubUK1K2ProjCup K1 K2).obj (unop U)))) ⟶ (op (unop U).2) := by
          apply op
          apply homOfLE
          simp
        rw [← colimit.w _ f]
        simp
        rfl-/
      | .one =>
        suffices F.val.map (op (homOfLE _)) ≫ colimit.ι (FU (K1 ⊓ K2) F.val) (op ((subK1SubK2toSubK1InterK2 K1 K2).obj (unop U))) = colimit.ι (FU (K1 ⊓ K2) F.val) (op ((K1subK2subU _ (opHomOfLE _).unop).obj ((K1subK2subU _ (opHomOfLE _).unop).obj ((KsubUK1K2ProjCup K1 K2).obj (unop U))))) by simpa [FSuptoFLeft, FtoFInfLeft, colimLimFUInterWCFlipIsColim]

        forceColimW
        /-have f : (op ((K1subK2subU _ (opHomOfLE ((by simp))).unop).obj
        ((K1subK2subU _ (opHomOfLE (FSuptoFLeft._proof_1 K1 K2)).unop).obj ((KsubUK1K2ProjCup K1 K2).obj (unop U))))) ⟶ (op ((subK1SubK2toSubK1InterK2 K1 K2).obj (unop U))) := by
          apply op
          apply homOfLE
          exact inf_le_sup
        rw [← colimit.w _ f]
        simp
        rfl-/

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
    apply @asIso _ _ _ _ _ (isIso_ι_of_isTerminal (IsTerminalKsubUOpBotOp) (FU ⊥ F.val ))
  ksh2 K1 K2 := by

    apply Limits.IsLimit.ofIsoLimit _ (SquareSuptoInfIsColimLim F K1 K2)
    apply IsLimit.ofPreservesConeTerminal

    exact IsLimitConeOfColimF (limFUInterWCFlip F.val K1 K2) (colimFUInterWC F.val K1 K2) _ (limColimFUCap K1 K2 F) (limFUInterWCFlipLim K1 K2 F) (colimFUInterWCColim F.val K1 K2) _ (limColimFUCapIsLim K1 K2 F)
    --OUIIIIIIIII
  ksh3 K := by
    apply Limits.IsColimit.ofIsoColimit _ (FLToKIsoToColimColim _ ).symm
    apply IsColimit.ofPreservesCoconeInitial

    apply colimIsColimColim _ _ (repOEx K) (repHEx K) (repLiftingEx K) _
    exact colimit.isColimit (FcupIaEx K F.val)

/-- α^* as a functor restricted to sheaves and corestricted to Ksheaves-/
@[simps]
def shAlphaUpStar : Sheaf C (of X) ⥤ (Ksheaf X C)  where
  obj G := shAlphaUpStarG X C G
  map f := (AlphaUpStar).map ((Sheaf.forget _ _).map f)
  map_id G := by
    -- j'ai remplace Sheaf.forget F par F.val pour simplifier et du coup il ne sait plus faire ça

    have : 𝟙 ((Sheaf.forget C (of X)).obj G) = 𝟙 G.val := by rfl
    rw [(Sheaf.forget C (of X)).map_id, this, AlphaUpStar.map_id]
    rfl

--Restrict the adjunction
/-- The adjunction between α^* and α_* restricted to sheaves and Ksheaves-/
def AdjShAlphaStar: (shAlphaUpStar X C ) ⊣ (shAlphaDownStar X C) := by
  apply (Adjunction.restrictFullyFaithful  (@AdjAlphaStar (of X) _ C _ _ _) _ _) _ _

  apply Sheaf.forget
  apply (inducedFunctor (fun (F:Ksheaf X C) => F.carrier))
  apply @Functor.FullyFaithful.ofFullyFaithful _ _ _ _ _ (Sheaf.forget_full _ _) (Sheaf.forgetFaithful _ _)

  apply fullyFaithfulInducedFunctor
  exact ⟨𝟙 _,𝟙 _,by aesop_cat,by aesop_cat⟩
  exact ⟨𝟙 _,𝟙 _,by aesop_cat,by aesop_cat⟩

--adjonction donne une équivalence de catégorie

#check IsIso ((Adjunction.unit (AdjShAlphaStar X C)).app F)

--variable  [ConcreteCategory C] [(forget C).ReflectsIsomorphisms ] [PreservesLimits (forget C)] [PreservesFilteredColimits (forget C)]
/- sur d'avoir besoin de tout ça?, en tout cas pour stalk iso functeur oui-/

-- c'est l'autre qu'il faut faire en premier
variable (G : Ksheaf X C) (F : Sheaf C (of X)) -- in order to get the variable in the right place for next theorems

theorem IsoAlphaUnit : IsIso ((AdjShAlphaStar X C).unit.app F):= by
  /-have truc : ∀ (x : ↑(of X)), IsIso ((stalkFunctor C x).map ((AdjShAlphaStar X C).unit.app F).val):= by
    intro p
    rw [← Adjunction.homEquiv_id]
    simp

    sorry-/ -- soucis d'univers mais il faudrait se passer des stalks cf argument de joel riou
  sorry

  --apply Presheaf.isIso_of_stalkFunctor_map_iso


  --rw [← Adjunction.homEquiv_id]
  --#check (AdjShAlphaStar X C).unit.app F

  --#check ((𝟭 (TopCat.Sheaf C (of X))).obj F : Functor _ _)
  --#check NatTrans.isIso_iff_isIso_app ((AdjShAlphaStar X C).unit.app F)

  --sorry





  --apply asIso

  --unfold AdjShAlphaStar AdjAlphaStar
  --simp
  --#check (NatTrans.isIso_iff_isIso_app ((Adjunction.unit (AdjShAlphaStar X)).app F)).2

/-def machin : (𝟭 (Ksheaf X C)).obj G ⟶ (shAlphaDownStar X C ⋙ shAlphaUpStar X C).obj G  where
  app K := by
    simp
    sorry-/




#check (AdjShAlphaStar X C).counit.app G

theorem IsoAlphaCoUnit :IsIso ((AdjShAlphaStar X C).counit.app G):= by

  --unfold AdjShAlphaStar AlphaDownStar
  --simp


  --#check  TopCat.Presheaf.isIso_of_stalkFunctor_map_iso
  sorry

/-- The isomorphism between the category of sheaves and the category of Ksheaves-/
def KshIsoSh: (Sheaf C (of X)) ≌ (Ksheaf X C) := by
   apply @Adjunction.toEquivalence _ _ _ _  _  _ (AdjShAlphaStar X C) (IsoAlphaUnit X C) (IsoAlphaCoUnit X C)

--#lint
