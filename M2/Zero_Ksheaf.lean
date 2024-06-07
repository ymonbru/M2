import M2.Ksheaves

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite

variable (X) [TopologicalSpace X] [T2Space X]

open ZeroObject

noncomputable section


def FZero:(Compacts X)ᵒᵖ ⥤ Ab where
  obj _ := 0
  map _ := 0

def ZKsheaf : (Ksheaf X) where
  F := (FZero X)
  ksh2 := by
    intros K1 K2
    unfold FZero complex plusFtoFcap FcuptoplusF ZtoFcup
    simp
    unfold ComposableArrows.precomp ComposableArrows.Precomp.map
    simp
    sorry

  ksh3:= sorry

#check ZKsheaf
