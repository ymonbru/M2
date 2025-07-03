import M2.alpha
import M2.colimOfColimEqColim
import M2.LimOfColimEx
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

variable (G : Ksheaf X C) (F : Sheaf C (of X))

noncomputable section

@[simp]
theorem KshToSh: IsSheaf  ((AlphaDownStar).obj (G.carrier) : Presheaf C (of X)):= by
  --probablement mieux d'utiliser isSheaf_iff_isSheafPairwiseIntersections
  apply (isSheaf_iff_isSheafPairwiseIntersections _).2
  unfold IsSheafPairwiseIntersections
  intro i U
  apply Nonempty.intro
  constructor
  · intro s j
    sorry
  · sorry
  · sorry


@[simps]
def shAlphaDownStarF : Sheaf C (of X) where
  val:= (AlphaDownStar).obj (G.carrier)
  cond := (KshToSh X C G)

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

@[simps!]
def TerminalOpBotsubU : IsTerminal (op ⟨⊥ , by simp⟩ : (KsubU_cat (⊥ : Compacts X) trueCond)ᵒᵖ ) := by
  apply terminalOpOfInitial
  apply IsInitial.ofUniqueHom
  · intro _ _
    apply eq_of_comp_right_eq
    intro _ _
    rfl
  · intro
    apply homOfLE
    intro x hx
    rcases hx


variable (K : Compacts X)

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



@[simps]
def FLToKIsoToColimColim {K :Compacts X} : (FLToFK K (AlphaUpStar.obj (F.val))) ≅ (Cocones.precomposeEquivalence (AlphaUpFIsoColimFSubU _ _ _ _ )).functor.obj (fCupIaCoconeToColimFiaCocone _ _ (colimit.cocone (FcupIaEx K F.val))) where
  hom := ⟨𝟙 (colimit (FU K F.val trueCond)), by aesop⟩
  inv := ⟨𝟙 (colimit (FcupIaEx K F.val)), by aesop⟩

variable (K1 K2 : Compacts X) [HasForget C]  [(forget C).ReflectsIsomorphisms] [HasFiniteLimits C] [PreservesColimitsOfShape (KsubU_cat K1 trueCond × KsubU_cat K2 trueCond)ᵒᵖ (forget C)] [PreservesFiniteLimits (forget C)] [Small.{v, w} (KsubU_cat K1 trueCond × KsubU_cat K2 trueCond)ᵒᵖ]
--par exemple le cas si C = Type w

#check IsLimitConeOfColimF (limFUInterWCFlip F.val K1 K2) (colimFUInterWC F.val K1 K2) (colimLimFUInterWCFlip K1 K2 F) (limColimFUCap K1 K2 F) (limFUInterWCFlipLim K1 K2 F) (colimFUInterWCColim F.val K1 K2) (colimLimFUInterWCFlipIsColim K1 K2 F) (limColimFUCapIsLim K1 K2 F)

#check ConeOverColimLimF (limFUInterWCFlip F.val K1 K2) (colimFUInterWC F.val K1 K2) (colimLimFUInterWCFlip K1 K2 F) (colimLimFUInterWCFlipIsColim K1 K2 F)

#check PullbackCone (FtoFInfLeft (AlphaUpStar.obj F.val) K1 K2) (FtoFInfRight (AlphaUpStar.obj F.val) K1 K2)

@[simps!]
def KsubUK1K2ProjLeft : (KsubU_cat K1 trueCond × KsubU_cat K2 trueCond) ⥤ (KsubU_cat K1 trueCond) := (CategoryTheory.Prod.fst (KsubU_cat K1 trueCond) (KsubU_cat K2 trueCond))


instance : (KsubUK1K2ProjLeft X K1 K2).Initial := by
  apply (Functor.initial_iff_of_isCofiltered _).mpr
  constructor
  · intro U
    use ⟨ U, ⊤⟩
    apply Nonempty.intro
    exact  𝟙 _
  · intro _ V _ _
    use V
    use 𝟙 _
    rfl

@[simps!]
def KsubUK1K2ProjRight: (KsubU_cat K1 trueCond × KsubU_cat K2 trueCond) ⥤ (KsubU_cat K2 trueCond) := (CategoryTheory.Prod.snd (KsubU_cat K1 trueCond) (KsubU_cat K2 trueCond))

instance : (KsubUK1K2ProjRight X K1 K2).Initial := by
  apply (Functor.initial_iff_of_isCofiltered _).mpr
  constructor
  · intro U
    use ⟨ ⊤, U⟩
    apply Nonempty.intro
    exact  𝟙 _
  · intro _ V _ _
    use V
    use 𝟙 _
    rfl

instance : (@subK1SubK2toSubK1InterK2 _ _ K1 K2).Initial := by
  apply (Functor.initial_iff_of_isCofiltered _).mpr
  constructor
  · intro U
    -- c'est au moins vrai dans les metriques en épaissisant
    sorry
  · intro _ V _ _
    use V
    use 𝟙 _
    rfl

@[simps!]
def jCompFEqProjCompFULeft : (jLeft K1 K2 ⋙ F.val) ≅ (KsubUK1K2ProjLeft X K1 K2).op ⋙ (FU K1 F.val trueCond) := eqToIso (by aesop)

@[simps!]
def jCompFEqProjCompFURight : (jRight K1 K2 ⋙ F.val) ≅ (KsubUK1K2ProjRight X K1 K2).op ⋙ (FU K2 F.val trueCond) := eqToIso (by aesop)

@[simps!]
def jCompFEqProjCompFUOne : (jOne K1 K2 ⋙ F.val) ≅ subK1SubK2toSubK1InterK2.op ⋙ (FU (K1 ⊓ K2) F.val trueCond) := eqToIso (by aesop)


def bidule : (colimFUInterWC F.val K1 K2).pt ⟶ cospan (FtoFInfLeft (AlphaUpStar.obj F.val) K1 K2) (FtoFInfRight (AlphaUpStar.obj F.val) K1 K2) := by
  refine natTransWcspFunc _ _ ?_ ?_ ?_ ?_ ?_
  · exact (HasColimit.isoOfNatIso (jCompFEqProjCompFULeft X C F K1 K2) ≪≫ Functor.Final.colimitIso (KsubUK1K2ProjLeft X K1 K2).op (FU K1 F.val trueCond)).hom
    --exact Iso.hom (HasColimit.isoOfNatIso (jCompFEqProjCompFULeft X C F K1 K2)) ≫ colimit.pre _ _
  · exact (HasColimit.isoOfNatIso (jCompFEqProjCompFURight X C F K1 K2) ≪≫ Functor.Final.colimitIso (KsubUK1K2ProjRight X K1 K2).op (FU K2 F.val trueCond)).hom
  · exact (HasColimit.isoOfNatIso (jCompFEqProjCompFUOne X C F K1 K2) ≪≫ Functor.Final.colimitIso subK1SubK2toSubK1InterK2.op (FU (K1 ⊓ K2) F.val trueCond)).hom
  · apply colimit.hom_ext
    intro U
    suffices F.val.map ((jLToJO K1 K2).app U) ≫
    colimit.ι (FU (K1 ⊓ K2) F.val trueCond) (op (subK1SubK2toSubK1InterK2.obj (unop U))) = colimit.ι (FU (K1 ⊓ K2) F.val trueCond) (op ((K1subK2subU trueCond (opHomOfLE _).unop).obj (unop U).1)) by simpa [FtoFInfLeft]


    have f : (op ((K1subK2subU trueCond (opHomOfLE (FtoFInfLeft._proof_1 K1 K2)).unop).obj (unop U).1)) ⟶ (op (subK1SubK2toSubK1InterK2.obj (unop U))) := by
      apply op
      apply homOfLE
      simp
    rw [← colimit.w _ f]
    suffices F.val.map ((jLToJO K1 K2).app U) ≫
    colimit.ι (FU (K1 ⊓ K2) F.val trueCond) (op (subK1SubK2toSubK1InterK2.obj (unop U))) = F.val.map f.unop.op ≫ colimit.ι (FU (K1 ⊓ K2) F.val trueCond) (op (subK1SubK2toSubK1InterK2.obj (unop U))) by simpa
    rfl
  · apply colimit.hom_ext
    intro U
    simp [FtoFInfRight]

    have f : (op ((K1subK2subU trueCond (opHomOfLE (FtoFInfRight._proof_1 K1 K2)).unop).obj (unop U).2)) ⟶ (op (subK1SubK2toSubK1InterK2.obj (unop U))) := by
      apply op
      apply homOfLE
      simp
    rw [← colimit.w _ f]
    suffices F.val.map ((jRToJO K1 K2).app U) ≫
    colimit.ι (FU (K1 ⊓ K2) F.val trueCond) (op (subK1SubK2toSubK1InterK2.obj (unop U))) = F.val.map f.unop.op ≫ colimit.ι (FU (K1 ⊓ K2) F.val trueCond) (op (subK1SubK2toSubK1InterK2.obj (unop U))) by simpa
    rfl

@[simps!]
def shAlphaUpStarG : (Ksheaf X C) where
  carrier:= (AlphaUpStar).obj F.val
  ksh1 := by
    have : IsTerminal ((F.val).obj (op (⊥ : Opens X))) := by
      apply Sheaf.isTerminalOfBotCover F (⊥ : Opens X)
      intro _ hx
      rcases hx
    apply IsTerminal.ofIso this
    apply @asIso _ _ _ _ _ (isIso_ι_of_isTerminal (TerminalOpBotsubU X) (FU ⊥ F.val trueCond))
  ksh2 K1 K2 := by
    --apply Limits.IsLimit.ofIsoLimit _
    --exact IsLimitConeOfColimF (limFUInterWCFlip F.val K1 K2) (colimFUInterWC F.val K1 K2) (colimLimFUInterWCFlip K1 K2 F) (limColimFUCap K1 K2 F) (limFUInterWCFlipLim K1 K2 F) (colimFUInterWCColim F.val K1 K2) (colimLimFUInterWCFlipIsColim K1 K2 F) (limColimFUCapIsLim K1 K2 F)

    #check colimitLimitIso
    unfold AlphaUpStar AlphaUpStarP AlphaUpStarF
    unfold SquareSuptoInf
    #check Sheaf.isLimitPullbackCone F
    #check F.val
    simp
    sorry
  ksh3 K := by
    apply Limits.IsColimit.ofIsoColimit _ (FLToKIsoToColimColim  X _ _ ).symm
    apply IsColimit.ofPreservesCoconeInitial

    apply colimIsColimColim _ _ (repOEx K) (repHEx K) (repLiftingEx K) _
    exact colimit.isColimit (FcupIaEx K F.val)



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

/- c'est l'autre qu'il faut faire en premier-/
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

def machin : (𝟭 (Ksheaf X C)).obj G ⟶ (shAlphaDownStar X C ⋙ shAlphaUpStar X C).obj G  where
  app K := by
    simp
    sorry




#check (AdjShAlphaStar X C).counit.app G

theorem IsoAlphaCoUnit :IsIso ((AdjShAlphaStar X C).counit.app G):= by

  --unfold AdjShAlphaStar AlphaDownStar
  --simp


  --#check  TopCat.Presheaf.isIso_of_stalkFunctor_map_iso
  sorry


def KshIsoSh: (Sheaf C (of X)) ≌  (Ksheaf X C) := by
   apply @Adjunction.toEquivalence _ _ _ _  _  _ (AdjShAlphaStar X C) (IsoAlphaUnit X C) (IsoAlphaCoUnit X C)
