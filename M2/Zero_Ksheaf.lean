import M2.Ksheaves
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite

variable {X} [TopologicalSpace X] [T2Space X]
variable (C) [Category C] [HasPullbacks C] [HasColimits C] [HasZeroObject C] [HasZeroMorphisms C]
--the condition of having 0 map is a consequence of having a 0:C but the mathlib page of hasZeroMorphism says it's better to do that
variable (K : Compacts X)

open ZeroObject Zero

noncomputable section

/-- The constant functor equal to 0-/
@[simp]
def FZero : (Compacts X)ᵒᵖ ⥤ C where-- := 0 does not allow aesop to deduce following facts
  obj _ := 0
  map _ := 0

/--The cocone of the diagram FUbar given by the zero maps-/
@[simps]
def zC:Cocone <| FUbar _ K (FZero C):=Cocone.mk 0 0

/-- The fact that the cocone zC satisfy the universal property-/
def zCisCol : IsColimit (zC C K) where
  desc _ := 0

/--The colimit of the diagram FUbar is the zero cocone-/
def zeroCocone : ColimitCocone <| FUbar _ K (FZero C) where
  cocone:= zC _ _
  isColimit := zCisCol _ _

/--The functor FZero gives rise to a Ksheaf-/
def ZKsheaf : Ksheaf X C where
  carrier := FZero C
  ksh1 := by simp
  ksh2 K K' := by
    apply PullbackCone.isLimitAux _ 0
    · intro s
      suffices 0 = s.fst by simpa
      apply Eq.symm
      apply IsZero.eq_zero_of_tgt (isZero_zero _)
    · intro s
      suffices 0 = s.snd by simpa
      apply Eq.symm
      apply IsZero.eq_zero_of_tgt (isZero_zero _)
    · intro s m _
      apply IsZero.eq_zero_of_tgt (isZero_zero _)
  ksh3 K := by
    constructor
    · intro _ _
      exact HasZeroObject.from_zero_ext_iff.mpr trivial
    · intro _ _ _
      exact HasZeroObject.from_zero_ext_iff.mpr trivial
    · intro _
      exact 0

instance : Inhabited (Ksheaf X C) where
  default := ZKsheaf C

#check colimit.isoColimitCocone

#lint
