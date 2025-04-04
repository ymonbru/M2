import M2.Ksheaves
import M2.alpha
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.OpensLeCover
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.CategoryTheory.Limits.Fubini
import Mathlib.CategoryTheory.Limits.Final


open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite TopCat TopCat.Presheaf
open ZeroObject

universe u v w-- Pas de w à cause des faisceaux

variable (X: Type w) [TopologicalSpace X] [T2Space X]
variable (C : Type u) [Category.{v, u} C] [HasColimitsOfSize.{w,w} C] [HasLimitsOfSize.{w,w} C] [HasColimits C]

variable (G: Ksheaf X C) (F:Sheaf C (of X))

noncomputable section

#check TopCat.Presheaf.IsSheaf ((AlphaDownStar).obj (G.carrier):Presheaf C (of X))

@[simp]
theorem KshToSh: TopCat.Presheaf.IsSheaf  ((AlphaDownStar).obj (G.carrier) : Presheaf C (of X)):= by
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





  /-apply (isSheaf_iff_isSheafOpensLeCover _).2
  unfold IsSheafOpensLeCover
  intro i U
  simp
  apply Nonempty.intro
  apply @IsLimit.mk _ _ _ _ _ _ _ _ _

  intro s
  repeat sorry-/

  /-unfold SheafCondition.opensLeCoverCocone AlphaDownStar AlphaDownStarG --iSup
  simp

  apply CategoryStruct.comp _

  apply limit.lift
  apply Cone.mk s.pt
  apply NatTrans.mk
  sorry
  intro K
  simp
  unfold GK
  simp
  let f:= s.π.app sorry
  unfold AlphaDownStar AlphaDownStarG at f
  simp at f

  sorry
  repeat sorry-/


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



@[simps!]
def shAlphaUpStarG : (Ksheaf X C) where
  carrier:= (AlphaUpStar).obj ((Sheaf.forget _ _).obj F)
  ksh1 := by
    have : IsTerminal ((F.val).obj (op (⊥ : Opens X))) := by
      apply Sheaf.isTerminalOfBotCover F (⊥ : Opens X)
      intro _ hx
      rcases hx
    apply IsTerminal.ofIso this
    apply @asIso _ _ _ _ _ (isIso_ι_of_isTerminal (TerminalOpBotsubU X) (FU ⊥ ((Sheaf.forget C (of X)).obj F) trueCond))
  ksh2 K1 K2 := by
    #check Sheaf.isLimitPullbackCone F

    --simp
    sorry
  ksh3 K := by
    --apply (Functor.Final.isColimitWhiskerEquiv _ _).toFun

    #check FresSSK K (AlphaUpStar.obj ((Sheaf.forget C (of X)).obj F))




    let Fp := (Sheaf.forget C (of X)).obj F
    let truc  := ((Functor.const _).obj (FU K Fp trueCond) : (supSupK_cat K)ᵒᵖ  ⥤ (KsubU_cat K trueCond)ᵒᵖ ⥤ C)

    let machin := colimitUncurryIsoColimitCompColim truc


    sorry






    /-constructor
    · sorry
    · sorry
    · intro s
      unfold FresSSK AlphaUpStar AlphaUpStarP at s
      simp at s
      simp
      have L : (supSupK_cat K)ᵒᵖ := sorry

      apply CategoryStruct.comp _
      exact s.ι.app L
      simp

      --have truc : (FU K ((Sheaf.forget C (of X)).obj F) trueCond) ⟶ (FU (unop L).obj ((Sheaf.forget C (of X)).obj F) trueCond) := by sorry

      have : colimit (((K1subK2subU trueCond K (unop L).obj sorry).op).comp (FU K ((Sheaf.forget C (of X)).obj F) trueCond)) = colimit (FU (unop L).obj ((Sheaf.forget C (of X)).obj F) trueCond) := by rfl--sorry

      rw [← this]

      --argh c'est le mauvais sens-/

#check lim.comp lim

@[simps]
def shAlphaUpStar : Sheaf C (of X) ⥤ (Ksheaf X C)  where
  obj G:= shAlphaUpStarG X C G
  map f:= (AlphaUpStar).map ((Sheaf.forget _ _).map f)


--Restrict the adjunction

def AdjShAlphaStar: (shAlphaUpStar X C ) ⊣ (shAlphaDownStar X C) := by
  apply (Adjunction.restrictFullyFaithful  (@AdjAlphaStar (of X) _ C _ _ _) _ _) _ _

  apply Sheaf.forget
  apply (inducedFunctor (fun (F:Ksheaf X C) => F.carrier))
  apply @Functor.FullyFaithful.ofFullyFaithful _ _ _ _ _ (TopCat.Sheaf.forget_full _ _) (TopCat.Sheaf.forgetFaithful _ _)

  apply fullyFaithfulInducedFunctor
  exact ⟨𝟙 _,𝟙 _,by aesop_cat,by aesop_cat⟩
  exact ⟨𝟙 _,𝟙 _,by aesop_cat,by aesop_cat⟩

--adjonction donne une équivalence de catégorie

#check IsIso ((Adjunction.unit (AdjShAlphaStar X C)).app F)

--variable  [ConcreteCategory C] [(forget C).ReflectsIsomorphisms ] [PreservesLimits (forget C)] [PreservesFilteredColimits (forget C)]
/- sur d'avoir besoin de tout ça?, en tout cas pour stalk iso functeur oui-/

/- c'est l'autre qu'il faut faire en premier-/
theorem IsoAlphaUnit :IsIso ((AdjShAlphaStar X C).unit.app F):= by
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
