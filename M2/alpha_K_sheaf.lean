import Mathlib
import Mathlib.Topology.Separation
import M2.Ksheaves
import M2.alpha

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite TopCat TopCat.Presheaf
open ZeroObject

variable (X) [TopologicalSpace X] [T2Space X]
variable (G:Ksheaf X) (F:Sheaf Ab (of X))

noncomputable section

theorem KshToSh: @Presheaf.IsSheaf _ _ (of X) ((AlphaDownStar X).obj (G.carrier):Presheaf _ (of X)):= by
  apply (isSheaf_iff_isSheafOpensLeCover _).2
  unfold IsSheafOpensLeCover
  intro i U
  simp
  apply Nonempty.intro
  apply @IsLimit.mk _ _ _ _ _ _ _ _ _

  intro s
  unfold SheafCondition.opensLeCoverCocone AlphaDownStar AlphaDownStarG --iSup
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


def shAlphaDownStarF : Sheaf Ab (of X) where
  val:= (AlphaDownStar X).obj (G.carrier)
  cond := (KshToSh X G)


def shAlphaDownStar : (Ksheaf X) ⥤ Sheaf Ab (of X) where
  obj G:= shAlphaDownStarF X G
  map f:= Sheaf.Hom.mk ((AlphaDownStar X).map f)
  map_id:= by
    intro _
    apply Sheaf.Hom.ext
    apply (AlphaDownStar X).map_id
  map_comp:= by
    intro _ _ _ _ _
    apply Sheaf.Hom.ext
    apply (AlphaDownStar X).map_comp


def shAlphaUpStarG : (Ksheaf X) where
  carrier:= (AlphaUpStar X).obj ((Sheaf.forget _ _).obj F)
  ksh1:= by
    unfold AlphaUpStar AlphaUpStarF --FU KsubU
    simp
    have :((Sheaf.forget _ _).obj F).obj (op (⊥:Opens X)) = 0:= by
      sorry
    rw [← this]
    sorry
  ksh2:= sorry
  ksh3:= by
    sorry


def shAlphaUpStar : Sheaf Ab (of X)⥤ (Ksheaf X)  where
  obj G:= shAlphaUpStarG X G
  map f:= (AlphaUpStar X).map ((Sheaf.forget _ _).map f)


--Restrict the adjunction

def AdjShAlphaStar: (shAlphaUpStar X ) ⊣ (shAlphaDownStar X ) := by
  apply (Adjunction.restrictFullyFaithful _ _ (AdjAlphaStar X) _ _)
  apply Sheaf.forget
  apply (inducedFunctor (fun (F:Ksheaf X) => F.carrier))
  apply @Functor.FullyFaithful.ofFullyFaithful _ _ _ _ _ (TopCat.Sheaf.forget_full _ _) (TopCat.Sheaf.forgetFaithful _ _)

  apply fullyFaithfulInducedFunctor
  exact ⟨𝟙 _,𝟙 _,by aesop_cat,by aesop_cat⟩
  exact ⟨𝟙 _,𝟙 _,by aesop_cat,by aesop_cat⟩

--adjonction donne une équivalence de catégorie

#check IsIso ((Adjunction.unit (AdjShAlphaStar X)).app F)


theorem IsoAlphaCoUnit :IsIso ((AdjShAlphaStar X).unit.app F):= by

  --unfold AdjShAlphaStar AdjAlphaStar
  --simp
  --#check (NatTrans.isIso_iff_isIso_app ((Adjunction.unit (AdjShAlphaStar X)).app F)).2

  sorry

theorem IsoAlphaUnit :IsIso ((AdjShAlphaStar X).counit.app G):= by
  --unfold AdjShAlphaStar AlphaDownStar
  --simp
  --#check  Presheaf.isIso_of_stalkFunctor_map_iso
  sorry


def KshIsoSh: (Sheaf Ab (of X)) ≅  (Ksheaf X):= by
  #check   @Adjunction.toEquivalence _ _ _ _  _  _ (AdjShAlphaStar X) (IsoAlphaCoUnit X) (IsoAlphaUnit X)
  --pourquoi ça ne convient pas
