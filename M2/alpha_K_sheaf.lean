import Mathlib
import Mathlib.Topology.Separation
import M2.Ksheaves
import M2.alpha

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite TopCat
open ZeroObject

variable (X) [TopologicalSpace X] [T2Space X]
variable (F:Ksheaf X)

noncomputable section

theorem KshToSh: @Presheaf.IsSheaf _ _ (of X) ((AlphaDownStar X).obj (F.carrier):Presheaf _ (of X)):= by sorry

variable (G:Presheaf Ab (of X))

def shAlphaDownStarF : Sheaf Ab (of X) where
  val:= (AlphaDownStar X).obj (F.carrier)
  cond := (KshToSh X F)


def shAlphaDownStar : (Ksheaf X) ⥤ Sheaf Ab (of X) where
  obj F:= shAlphaDownStarF X F
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
  carrier:= (AlphaUpStar X).obj (G)
  ksh1:= by
    unfold AlphaUpStar AlphaUpStarF --FU KsubU
    simp
    have :G.obj (op (⊥:Opens X)) = 0:= by
      sorry

    sorry
  ksh2:= sorry
  ksh3:= sorry


def shAlphaUpStar : Sheaf Ab (of X)⥤ (Ksheaf X)  where
  obj G:= shAlphaUpStarG X ((Sheaf.forget _ _).obj G)
  map f:= (AlphaUpStar X).map ((Sheaf.forget _ _).map f)


--Restrict the adjunction

def ShForgetAlphaToShAlphatForget :Sheaf.forget Ab (of X) ⋙  AlphaUpStar X ⟶  shAlphaUpStar X ⋙ (inducedFunctor fun (F:Ksheaf X) ↦ F.carrier) where
app F:= by
  simp
  unfold shAlphaUpStar shAlphaUpStarG
  exact 𝟙 _

def ShAlphatForgetToShForgetAlpha :shAlphaUpStar X ⋙ (inducedFunctor fun (F:Ksheaf X) ↦ F.carrier)⟶ Sheaf.forget Ab (of X) ⋙  AlphaUpStar X where
app F := by
  simp
  unfold shAlphaUpStar shAlphaUpStarG
  exact 𝟙 _

def ShForgetAlphaIsoShAlphatForget :Sheaf.forget Ab (of X) ⋙  AlphaUpStar X ≅ shAlphaUpStar X ⋙ (inducedFunctor fun (F:Ksheaf X) ↦ F.carrier) where
hom:=ShForgetAlphaToShAlphatForget X
inv:=ShAlphatForgetToShForgetAlpha X
hom_inv_id:= by
  apply NatTrans.ext
  apply funext
  intro _
  unfold ShForgetAlphaToShAlphatForget ShAlphatForgetToShForgetAlpha
  rfl
inv_hom_id:= by
  apply NatTrans.ext
  apply funext
  intro _
  unfold ShForgetAlphaToShAlphatForget ShAlphatForgetToShForgetAlpha
  rfl

def ShForgetAlphatForgetToForgetAlpha :shAlphaDownStar X ⋙ Sheaf.forget Ab (of X) ⟶ (inducedFunctor fun (F:Ksheaf X) ↦ F.carrier) ⋙ AlphaDownStar X where
app F:= by
  simp
  unfold shAlphaDownStar shAlphaDownStarF
  exact 𝟙 _

def ForgetAlphaToShForgetAlphatForget :(inducedFunctor fun (F:Ksheaf X) ↦ F.carrier) ⋙ AlphaDownStar X ⟶  shAlphaDownStar X ⋙ Sheaf.forget Ab (of X) where
app F := by
  simp
  unfold shAlphaDownStar shAlphaDownStarF
  exact 𝟙 _

def ForgetAlphaIsoShForgetAlphatForget :(inducedFunctor fun (F:Ksheaf X) ↦ F.carrier) ⋙ AlphaDownStar X ≅ shAlphaDownStar X ⋙ Sheaf.forget Ab (of X) where
hom:=ForgetAlphaToShForgetAlphatForget X
inv:=ShForgetAlphatForgetToForgetAlpha X
hom_inv_id:= by
  apply NatTrans.ext
  apply funext
  intro _
  unfold ForgetAlphaToShForgetAlphatForget ShForgetAlphatForgetToForgetAlpha
  rfl
inv_hom_id:= by
  apply NatTrans.ext
  apply funext
  intro _
  unfold ShForgetAlphatForgetToForgetAlpha ForgetAlphaToShForgetAlphatForget
  rfl

def AdjShAlphaStar: (shAlphaUpStar X ) ⊣ (shAlphaDownStar X ) := by
  apply (Adjunction.restrictFullyFaithful _ _ (AdjAlphaStar X) _ _)
  apply Sheaf.forget
  apply (inducedFunctor (fun (F:Ksheaf X) => F.carrier))
  apply @Functor.FullyFaithful.ofFullyFaithful _ _ _ _ _ (TopCat.Sheaf.forget_full _ _) (TopCat.Sheaf.forgetFaithful _ _)

  apply fullyFaithfulInducedFunctor
  exact ShForgetAlphaIsoShAlphatForget X
  exact ForgetAlphaIsoShForgetAlphatForget X

--adjonction donne une équivalence de catégorie

def KshIsoSh: (Sheaf Ab (of X)) ≅  (Ksheaf X):= by
  #check Adjunction.toEquivalence


  sorry
