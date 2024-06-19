import Mathlib
import Mathlib.Topology.Separation
import M2.Ksheaves
import M2.alpha

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite TopCat

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

def shAlphaUpStarG : (KSheaf X) where
  carrier:= (AlphaDownStar X).obj (G)
  ksh1:= sorry
  ksh2:= sorry
  ksh3:= sorry


def shAlphaUpStar : Sheaf Ab (of X)⥤ (Ksheaf X)  where
  obj G:= shAlphaUpStarG X G
  map f:= Sheaf.Hom.mk ((AlphaUpStar X).map f)
  map_id:= by
    sorry
  map_comp:= by
    sorry
