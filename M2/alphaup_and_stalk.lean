import Mathlib
import Mathlib.Topology.Separation
import M2.alpha
import M2.K_stalks

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite TopCat TopCat.Presheaf
open ZeroObject

variable (X) [TopologicalSpace X] [T2Space X]
variable (p:X) (F:Presheaf Ab (of X))


noncomputable section

#check Functor.comp (AlphaUpStar) (KstalkFunctor p)
#check @stalkFunctor Ab _ _ (of X) p

/--The natural maps from F(U) (fo U containing p) to the stalk of F at p-/
@[simps]
def FUtoStalkι : FU (pC p) F (trueCond ) ⟶ (Functor.const _ ).obj (F.stalk p) where
  app U := germ _ ⟨p, U.unop.property.1 (by rfl)⟩ ≫ F.stalkSpecializes (by rfl)

  naturality U V _ := by
    suffices F.map _ ≫ F.germ ⟨_, V.unop.property.1 (by rfl)⟩ = F.germ ⟨_, U.unop.property.1 (by rfl)⟩ by simpa
    apply Presheaf.germ_res

/-The cocone induced by FUtoStalkι-/
@[simps]
def FUtoStalk : Cocone (FU (pC p) F (trueCond)):= Cocone.mk _ (FUtoStalkι X p F)

variable (c:Cocone (FU (pC p) F trueCond))

instance :IsColimit (FUtoStalk X p F) where
  desc := by
    intro s
    simp
    unfold stalk stalkFunctor
    simp
    --apply colimit.desc
    sorry
  fac := by
    sorry
  uniq := by
    sorry



def AlphaComStalkEval : (AlphaUpStar) ⋙ (EvalInP p)⟶ @stalkFunctor _ _ _ (of X) p  where
  app F := colimit.desc _ (FUtoStalk _ _ _)
  naturality F1 F2 τ :=by
    suffices colimMap (τres ⟨{p},_⟩ _ _ _ _) ≫ colimit.desc _ (FUtoStalk _ _ _) = _ by simpa
    apply colimit.hom_ext
    intro j
    rw [← Category.assoc]
    unfold pC

    --suffices τ.app { unop := j.unop.obj } ≫ germ F2 ⟨p, _⟩ = germ F1 ⟨p, _⟩ ≫ (stalkFunctor Ab p).map τ by simpa
    --pourquoi cette erreur?
    simp

    rw [ Presheaf.stalkFunctor_map_germ]

def AlphaComStalk : (AlphaUpStar) ⋙ (KstalkFunctor p)⟶ @stalkFunctor Ab _ _ (of X) p := by
  apply CategoryStruct.comp _
  exact AlphaComStalkEval X p
  apply whiskerLeft (AlphaUpStar)
  exact (IsoAlphaUpPtoQ p).hom

instance : IsIso (AlphaComStalk X p):= by

  sorry

def IsoAlphaComStalk: (AlphaUpStar) ⋙ (KstalkFunctor p) ≅ @stalkFunctor Ab _ _ (of X) p:= asIso (AlphaComStalk X p)
