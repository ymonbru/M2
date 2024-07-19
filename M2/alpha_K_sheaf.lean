import M2.Ksheaves
import M2.alpha
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.OpensLeCover
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.Topology.Sheaves.Stalks

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite TopCat TopCat.Presheaf
open ZeroObject

variable (X) [TopologicalSpace X] [T2Space X]
variable (C) [Category C] [HasColimits C] [HasLimits C][HasZeroObject C]
variable (G:Ksheaf X C) (F:Sheaf C (of X))

noncomputable section

#check TopCat.Presheaf.IsSheaf ((AlphaDownStar).obj (G.carrier):Presheaf C (of X))

theorem KshToSh: TopCat.Presheaf.IsSheaf  ((AlphaDownStar).obj (G.carrier):Presheaf C (of X)):= by
  apply (isSheaf_iff_isSheafOpensLeCover _).2
  unfold IsSheafOpensLeCover
  intro i U
  simp
  apply Nonempty.intro
  apply @IsLimit.mk _ _ _ _ _ _ _ _ _

  intro s
  repeat sorry

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



def shAlphaDownStarF : Sheaf C (of X) where
  val:= (AlphaDownStar).obj (G.carrier)
  cond := (KshToSh X C G)


def shAlphaDownStar : (Ksheaf X C) ⥤ Sheaf C (of X) where
  obj _ := shAlphaDownStarF X C _
  map f := Sheaf.Hom.mk ((AlphaDownStar).map f)
  map_id _ := by
    apply Sheaf.Hom.ext
    apply (AlphaDownStar).map_id
  map_comp _ _:= by
    apply Sheaf.Hom.ext
    apply (AlphaDownStar).map_comp


def shAlphaUpStarG : (Ksheaf X C) where
  carrier:= (AlphaUpStar).obj ((Sheaf.forget _ _).obj F)
  ksh1:= by
    unfold AlphaUpStar AlphaUpStarP AlphaUpStarF--FU KsubU
    simp
    have :((Sheaf.forget _ _).obj F).obj (op (⊥:Opens X)) = 0:= by
      sorry
    rw [← this]
    sorry
  ksh2:= by
    sorry
  ksh3:= by
    sorry


def shAlphaUpStar : Sheaf C (of X)⥤ (Ksheaf X C)  where
  obj G:= shAlphaUpStarG X C G
  map f:= (AlphaUpStar).map ((Sheaf.forget _ _).map f)


--Restrict the adjunction

def AdjShAlphaStar: (shAlphaUpStar X C ) ⊣ (shAlphaDownStar X C) := by

  apply (Adjunction.restrictFullyFaithful _  _ (@AdjAlphaStar (of X) _ C _ _ _) _ _)
  apply Sheaf.forget
  apply (inducedFunctor (fun (F:Ksheaf X C) => F.carrier))
  apply @Functor.FullyFaithful.ofFullyFaithful _ _ _ _ _ (TopCat.Sheaf.forget_full _ _) (TopCat.Sheaf.forgetFaithful _ _)

  apply fullyFaithfulInducedFunctor
  exact ⟨𝟙 _,𝟙 _,by aesop_cat,by aesop_cat⟩
  exact ⟨𝟙 _,𝟙 _,by aesop_cat,by aesop_cat⟩

--adjonction donne une équivalence de catégorie

#check IsIso ((Adjunction.unit (AdjShAlphaStar X C)).app F)


theorem IsoAlphaCoUnit :IsIso ((AdjShAlphaStar X C).unit.app F):= by
  --apply @Presheaf.isIso_of_stalkFunctor_map_iso
  --apply asIso

  --unfold AdjShAlphaStar AdjAlphaStar
  --simp
  --#check (NatTrans.isIso_iff_isIso_app ((Adjunction.unit (AdjShAlphaStar X)).app F)).2

  sorry

#check (AdjShAlphaStar X C).counit.app G

theorem IsoAlphaUnit :IsIso ((AdjShAlphaStar X C).counit.app G):= by
  --unfold AdjShAlphaStar AlphaDownStar
  --simp


  #check  TopCat.Presheaf.isIso_of_stalkFunctor_map_iso
  sorry


def KshIsoSh: (Sheaf C (of X)) ≌  (Ksheaf X C) := by

   apply @Adjunction.toEquivalence _ _ _ _  _  _ (AdjShAlphaStar X C) (IsoAlphaCoUnit X C) (IsoAlphaUnit X C)


  --sorry
  --pourquoi ça ne convient pas? problème d'univers
