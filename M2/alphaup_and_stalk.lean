import M2.alpha
import M2.K_stalks
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.Sheaves.Stalks

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite TopCat TopCat.Presheaf
open ZeroObject

universe u v

variable (X : Type v) [TopologicalSpace.{v} X] [T2Space X]
variable {C : Type u} [Category.{v, u} C] [HasColimits C]
variable (p: of X) (F:Presheaf C (of X))


noncomputable section

#check Functor.comp (AlphaUpStar) (KstalkFunctor p)
#check @stalkFunctor C _ _ (of X) p

/-- Functor from the neighbourhoods of p to the opens that contains p-/
@[simp]
def NhdsToPsubU : (@OpenNhds (of X) p) ⥤ (KsubU_cat (pC p) trueCond) where
  obj U := ⟨U.1, Set.singleton_subset_iff.2 U.property,rfl⟩
  map f := ⟨homOfLE  (leOfHom f)⟩

/-- The natural maps from F(U) (fo U containing p) to the stalk of F at p-/
@[simps]
def FUtoStalkι : FU (pC p) F (trueCond ) ⟶ (Functor.const _ ).obj (F.stalk p) where
  app U := germ _ U.unop.obj p (U.unop.property.1 (by rfl)) ≫ F.stalkSpecializes (by rfl)

/-- The cocone induced by FUtoStalkι -/
@[simps]
def FUtoStalk : Cocone (FU (pC p) F (trueCond)):= Cocone.mk _ (FUtoStalkι X p F)

variable (c : Cocone (FU (pC p) F trueCond))


/-- The natural maps from F at the neighbourhood of to a cocone of F(U) for U containing p-/
@[simps]
def CoconeFUpCtoOPenNhdspι :(OpenNhds.inclusion p).op ⋙ F ⟶ (Functor.const _).obj c.pt where
  app U:= c.ι.app <| op <| (@NhdsToPsubU (of X) _ (p:of X)).obj U.unop
  naturality _ _ _ := by
    simp
    forceColimW

/-- The cocone indiced by the natural maps of CoconeFUpCtoOPenNhdspι -/
@[simps]
def CoconeFUpCtoOPenNhdsp : Cocone ((OpenNhds.inclusion p).op ⋙ F) := Cocone.mk _ (CoconeFUpCtoOPenNhdspι X p F c)

/-- The evidence that that the cocone (FUtoStalk X p F) is colimit-/
@[simps]
def IsColimitFUtoStalk :IsColimit (FUtoStalk X p F) where
  desc s := colimit.desc _ (CoconeFUpCtoOPenNhdsp X _ F s)
  fac s U := by
    suffices s.ι.app (op ⟨U.unop.obj,_⟩ ) = s.ι.app U by simpa [germ]
    rfl
  uniq s m hm := by
    apply Presheaf.stalk_hom_ext
    intro U hU
    suffices colimit.ι ((OpenNhds.inclusion p).op ⋙ F) (op ⟨U , _⟩) ≫ m = s.ι.app (op ⟨U , _⟩) by simpa [germ]
    rw [← hm ]
    simp [germ]

variable (C)

/-- The morphism of colimit.cocone to FUtoStalk -/
@[simps]
def ColimitToFUstalk :(colimit.cocone (FU (pC p) F trueCond)) ⟶ (FUtoStalk X p F) where
  hom  := colimit.desc _ (FUtoStalk _ _ _)

/-- The natural transformation from α ≫ evaluation in p to the stalk functor-/
def AlphaComStalkEval : (AlphaUpStar) ⋙ (EvalInP C p)⟶ @stalkFunctor _ _ _ (of X) p  where
  app F := (ColimitToFUstalk X C p F).hom

/-- The natural transformation from α ≫ stalk in p to the stalk functor. It's induced by AlphaComStalkEval and the isomorphism of evaluation in p and stalk in p for K-presheaves -/
def AlphaComStalk : (AlphaUpStar) ⋙ (KstalkFunctor p)⟶ @stalkFunctor C _ _ (of X) p := Functor.whiskerLeft _ (StalkToPFunc C p) ≫ AlphaComStalkEval _ _ _

instance : IsIso (AlphaComStalk X C p):= by
  suffices IsIso (AlphaComStalkEval X C p) by apply IsIso.comp_isIso
  apply ( NatTrans.isIso_iff_isIso_app _).2
  intro F
  suffices IsIso (ColimitToFUstalk X C p F) by
      rcases this.out with ⟨i,hi⟩
      use i.hom
      constructor
      · calc (ColimitToFUstalk X C p F).hom ≫ i.hom = ((ColimitToFUstalk X C p F) ≫ i).hom := rfl
        _= _ := by rw [hi.1]
        _ = _ := by rfl

      · calc i.hom ≫ (ColimitToFUstalk X C p F).hom = ( i ≫ (ColimitToFUstalk X C p F)).hom := rfl
        _= _ := by rw [hi.2]
        _ = _ := by rfl

  apply IsColimit.hom_isIso
  · exact colimit.isColimit _
  · exact IsColimitFUtoStalk X p F

/-- the evidence that the functor α*≫ Kstalk and stalk are isomorphics -/
def IsoAlphaComStalk: (AlphaUpStar) ⋙ (KstalkFunctor p) ≅ @stalkFunctor C _ _ (of X) p:= asIso (AlphaComStalk X C p)

--#lint
