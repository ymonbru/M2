import M2.Ksheaves

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite

variable {X} [TopologicalSpace X] [T2Space X]
variable (A) [Ring A]
variable (K : Compacts X)

open ZeroObject

noncomputable section

/-- The constant functor equal to 0-/
@[simps]
def FZero : (Compacts X)ᵒᵖ ⥤ ModuleCat A where-- ça n'a pas l'air de marcher := 0
  obj _ := 0
  map _ := 0

#check FUbar
--@[simps]
/--The cocone of the diagram FUbar given by the zero maps-/
def zC:Cocone <| FUbar _ K (FZero A):=Cocone.mk 0 0

/-- The fact that the cocone zC satisfy the universal property-/
def zCisCol : IsColimit (zC A K) where
  desc _ := 0
  fac _ _ := Eq.symm <| IsZero.eq_zero_of_src (isZero_zero _) _
  uniq _ _ _ := IsZero.eq_zero_of_src (isZero_zero _) _

/--The colimit of the diagram FUbar is the zero cocone-/
def zeroCocone : ColimitCocone <| FUbar _ K (FZero A) where
  cocone:= zC _ _
  isColimit := zCisCol _ _

/--The functor FZero gives rise to a Ksheaf-/
def ZKsheaf : Ksheaf X A where
  carrier := FZero A
  ksh1 := by simp
  ksh2 K K' := by
    unfold complex
    apply ComposableArrows.exact_of_δ₀
    · apply ComposableArrows.exact₂_mk
      · apply ShortComplex.exact_of_isZero_X₂
        apply isZero_zero
      · simp [ZtoFcup]

    · apply ComposableArrows.exact₂_mk
      · apply ShortComplex.exact_of_isZero_X₂
        simp [isZero_zero _]
      · simp [plusFtoFcap, FcuptoplusF]

  ksh3 _ := by
    apply isIso_of_source_target_iso_zero
    apply colimit.isoColimitCocone (zeroCocone _ _)
    rfl

instance : Inhabited (Ksheaf X A) where
  default := ZKsheaf A

#lint
