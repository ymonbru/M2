import M2.Ksheaves

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite

variable (X) [TopologicalSpace X] [T2Space X]
variable (K:Compacts X)

open ZeroObject

noncomputable section


def FZero:(Compacts X)ᵒᵖ ⥤ Ab where
  obj _ := 0
  map _ := 0

def zC:Cocone (FUbar X K (FZero X)):=Cocone.mk (0) (0)


def zCisCol : IsColimit (zC X K) where
  desc := by
    intro s
    exact 0
  fac := by
    intro s W
    rw [IsZero.eq_zero_of_src (isZero_zero Ab) (s.ι.app W)]
    simp
  uniq := by
    intro s m _
    apply IsZero.eq_zero_of_src (isZero_zero Ab)



def zeroCocone :ColimitCocone (FUbar X K (FZero X)) where
  cocone:= (@zC X _ _ K)
  isColimit := zCisCol X K

def ZKsheaf : (Ksheaf X) where
  carrier := (FZero X)
  ksh2 := by
    intros K1 K2

    unfold complex FZero plusFtoFcap FcuptoplusF ZtoFcup
    --simp
    apply ComposableArrows.exact_of_δ₀
    --deux fois le même bloc mais avec repeat ça ne marche pas

    apply ComposableArrows.exact₂_mk
    apply ShortComplex.exact_of_isZero_X₂
    --simp
    exact isZero_zero Ab
    apply ComposableArrows.IsComplex.zero
    apply ComposableArrows.isComplex₂_mk
    simp

    apply ComposableArrows.exact₂_mk
    apply ShortComplex.exact_of_isZero_X₂
    simp
    exact isZero_zero Ab
    apply ComposableArrows.IsComplex.zero
    apply ComposableArrows.isComplex₂_mk
    simp

  ksh3:= by
    intro K
    apply isIso_of_source_target_iso_zero

    apply colimit.isoColimitCocone (zeroCocone _ _)

    unfold FZero FK
    rfl



#check ZKsheaf
