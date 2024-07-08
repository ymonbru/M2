import Mathlib
import Mathlib.Topology.Separation
import M2.alpha
import M2.K_stalks

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite TopCat TopCat.Presheaf
open ZeroObject

variable (X) [TopologicalSpace X] [T2Space X]
variable (p:X) (F:Presheaf Ab (of X))


noncomputable section

#check Functor.comp (AlphaUpStar X) (KstalkFunctor X p)
#check @stalkFunctor Ab _ _ (of X) p

def trucι: FU X (pC X p) F (trueCond X) ⟶
  (Functor.const (KsubU_cat X (pC X p) (trueCond X))ᵒᵖ).obj (F.stalk p) where
  app U := by
    unfold FU
    simp

    --#check ⟨p,h⟩ : U.unop.obj
    apply @germ Ab _ _ (of X) F U.unop.obj _ ≫ _
    use p
    apply U.unop.property.1
    rfl
    apply F.stalkSpecializes
    rfl


    --sorry
  naturality := by
    intro U V f
    unfold FU
    simp
    sorry

def truc :Cocone (FU X (pC X p) F (trueCond X)) where
  pt := @stalk _ _ _ (of X) F p
  ι:= trucι X p F

def AlphaComStalkEval : (AlphaUpStar X) ⋙ (EvalInP X p)⟶ @stalkFunctor Ab _ _ (of X) p  where
  app F:= colimit.desc (FU X (pC X p) F (trueCond X)) (truc X p F)

  naturality F1 F2 τ:=by
    unfold EvalInP AlphaUpStar AlphaUpStarP AlphaUpStarTau τres truc trucι stalkFunctor
    simp
    apply colimit.hom_ext
    intro j
    simp


    sorry

def AlphaComStalk : (AlphaUpStar X) ⋙ (KstalkFunctor X p)⟶ @stalkFunctor Ab _ _ (of X) p := by
  apply CategoryStruct.comp _
  exact AlphaComStalkEval X p
  apply whiskerLeft (AlphaUpStar X)
  exact (IsoAlphaUpPtoQ X p).hom

instance : IsIso (AlphaComStalk X p):= by

  sorry

def IsoAlphaComStalk: (AlphaUpStar X) ⋙ (KstalkFunctor X p) ≅ @stalkFunctor Ab _ _ (of X) p:= asIso (AlphaComStalk X p)
