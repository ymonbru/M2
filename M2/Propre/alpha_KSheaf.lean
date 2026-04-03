import M2.Propre.alpha
import M2.LimOfColimEqColimOfLim
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite TopCat

universe u v w

noncomputable section

variable {A : Type u} [Category.{v, u} A] [HasLimitsOfSize.{w, w, v,u} A] [HasColimitsOfSize.{w, w, v, u} A] [AB5OfSize.{w, w, v, u} A]
variable {X : Type w} [TopologicalSpace X] [T2Space X]

namespace TopCat.Sheaf

open TopCat.Presheaf

--variable (F : Sheaf A (of X))

def toSheaf [AB5OfSize.{w, w, v, u} A]: Sheaf A (of X) ⥤ KSheaf A (of X) := by
  apply ObjectProperty.lift _ (Sheaf.forget A (of X) ⋙ toKPresheafFunctor)
  intro F
  constructor
  · apply Nonempty.intro
    have : IsTerminal (((Subtype.mono_coe (⊥ : Compacts X).openNhds).functor.op ⋙ (forget A (of X)).obj F).obj (op (⊥ : (⊥ : Compacts X).openNhds ))) := by
      apply Sheaf.isTerminalOfBotCover F (⊥ : Opens X)
      intro _ h
      rcases h
    apply IsTerminal.ofIso this
    apply @asIso _ _ _ _ (((forget A (of X)).obj F).ιToKPresheafFunctorObjObj (⊥ : (⊥ : Compacts X).openNhds )) (by
      apply isIso_ι_of_isTerminal _ _
      apply IsInitial.op
      exact instIsInitialElemOpensOpenNhdsBot)
  · intro K1 K2 K3 K4 h
    simp
    set F2 := (forget A (of X)).obj F
    constructor
    · apply Nonempty.intro

      let J := WalkingCospan
      let K := (K1.openNhds × K4.openNhds)ᵒᵖ
      let Diag : J ⥤ K ⥤ A := sorry

      #check IsLimitConeOfColimF (J := WalkingCospan) (K := (K1.openNhds × K4.openNhds)ᵒᵖ) (F := by


        sorry)


      sorry
    · constructor
      sorry
  · sorry

#min_imports
