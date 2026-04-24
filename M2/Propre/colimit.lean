import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import M2.Propre.unionCat

open CategoryTheory Limits

universe u1 v1 u2 v2 u3 v3 u4 v4

namespace CategoryTheory.Limits

variable {C : Type u1} [Category.{v1} C]
variable {J : Type u2} [Category.{v2} J]
variable {K : Type u3} [Category.{v3} K]
variable [HasLimitsOfShape J C] [HasColimitsOfShape K C]
variable [PreservesLimitsOfShape J (colim : (K ⥤ C) ⥤ _)]

variable {F : J ⥤ K ⥤ C}

variable (limF : Cone F) (colimF : Cocone F.flip) (colimLimF : Cocone limF.pt) (limColimF : Cone colimF.pt)

variable (hLimF : IsLimit limF) (hColimF : IsColimit colimF) (hColimLimF : IsColimit colimLimF) (hLimColimF : IsLimit limColimF)

/-- The isomorphism between limcolim F and colimLim F for any cone and cocones.
It's composition of (colimitLimitIso F) and the canonicals isomorphisms-/
noncomputable def limColimFPtIsoColimLimFPt : limColimF.pt ≅ colimLimF.pt := (IsLimit.conePointUniqueUpToIso hLimColimF (limit.isLimit colimF.pt)) ≪≫ HasLimit.isoOfNatIso (IsColimit.coconePointUniqueUpToIso hColimF (colimit.isColimit F.flip)) ≪≫ (colimitLimitIso F).symm ≪≫ HasColimit.isoOfNatIso (IsLimit.conePointUniqueUpToIso hLimF (limit.isLimit F)).symm ≪≫ (IsColimit.coconePointUniqueUpToIso hColimLimF (colimit.isColimit limF.pt)).symm

noncomputable def IsLimitConeOfColimF : IsLimit (Cone.extend _ (limColimFPtIsoColimLimFPt limF colimF colimLimF limColimF hLimF hColimF hColimLimF hLimColimF).inv) := IsLimit.extendIso _ hLimColimF

noncomputable def IsColimitCoconeOfLimF : IsColimit (Cocone.extend _ (limColimFPtIsoColimLimFPt limF colimF colimLimF limColimF hLimF hColimF hColimLimF hLimColimF).inv) := IsColimit.extendIso _ hColimLimF

end CategoryTheory.Limits

namespace CategoryTheory.Limits

open UnionCat

variable {A : Type u1} [Category.{v1, u1} A] {I : A ⥤ Cat.{v2, u2}} {D : Type u3} [Category.{v3, u3} D] {C : Type u4} [Category.{v4 ,u4} C] (sD : CoconeFunctor D I) (F : D ⥤ C)

variable [HasColimitsOfSize.{v2, u2} C]

set_option backward.isDefEq.respectTransparency false in
/-- if r anq s are two compatible then the morphism FcupIa.obj x → colimit induced by the two representation are compatible with the structure of diagram of colimFia-/
@[simp]
lemma FcupColimIndepOfLift {x : D}  (r s : repObj sD x) (l : lifting r s) : (F.map r.rep.inv ≫ colimit.ι ((sD.extend F).i r.a) r.ia) ≫ (sD.extend F).colim.map l.hom = F.map s.rep.inv ≫ colimit.ι ((sD.extend F).i s.a) s.ia := by
  have : s.rep.inv = r.rep.inv ≫ ((sD.iso l.hom).inv).app r.ia ≫ (sD.i s.a).map l.liftIso.hom := by
    rw [ ← l.compat]
    simp
  rw [this, F.map_comp]
  repeat rw [ Category.assoc]
  apply whisker_eq

  simp

  apply whisker_eq
  --here rw [← colimit.w ]; rfl works but we have the tactic...
  forceColimW

set_option backward.isDefEq.respectTransparency false in
/-If the representation r is a lifting of the representation q then the morphism _ ≫ colimit.ι _ ≫ colimit.ι _ is the same for r and q.
The lemma is valid for any cocone not just the colimit-/
@[simp]
lemma colimColimIndepOfLift (x : C) (s : Cocone (colimFia iaSubC FcupIa) ) (r q : repObj iaSubC x) (l : lifting iaSubC r q) : FcupIa.map r.rep.inv ≫ colimit.ι (iaSubC.i r.a ⋙ FcupIa) r.ia ≫ s.ι.app r.a = FcupIa.map q.rep.inv ≫ colimit.ι (iaSubC.i q.a ⋙ FcupIa) q.ia ≫ s.ι.app q.a := by
  have : (colimFia iaSubC FcupIa).map l.hom ≫ s.ι.app q.a = s.ι.app r.a := by
      rw [s.ι.naturality]
      simp
  rw [← this]
  repeat rw [← Category.assoc]
  apply eq_whisker
  apply FcupColimIndepOfLift

variable (repLifting : {x : C} → (r s : repObj iaSubC x) → (t : repObj iaSubC x) × (lifting iaSubC r t) × (lifting iaSubC s t))

/- Same statement as colimColimIndepOfLift with no hypothesis on r and q bu assuming there is a general construction that give a common lifting -/
include repLifting in
theorem colimColimIndep {x : C} (s : Cocone (colimFia iaSubC FcupIa) ) (r q : repObj iaSubC x) : FcupIa.map r.rep.inv ≫ colimit.ι (iaSubC.i r.a ⋙ FcupIa) r.ia ≫ s.ι.app r.a = FcupIa.map q.rep.inv ≫ colimit.ι (iaSubC.i q.a ⋙ FcupIa) q.ia ≫ s.ι.app q.a := by
  obtain ⟨t, lrt, lqt⟩ := repLifting r q
  rw [colimColimIndepOfLift _ _ _ _ _ t lrt]
  rw [colimColimIndepOfLift _ _ _ _ _ t lqt]

variable (uc: unionCat C i)

set_option backward.isDefEq.respectTransparency false in
/-- If s is a cocone for colimFia then it induces a cocone over FcupIa with the same point-/
@[simps!]
def colimColimFiaCoconeFcupIa (uc: unionCat C i) (s : Cocone (colimFia uc.iaSubC FcupIa) ) : Cocone FcupIa where
  pt := s.pt
  ι.app x:=
  let xr := uc.repO x;
    (FcupIa.map xr.rep.inv ≫ colimit.ι (uc.iaSubC.i xr.a ⋙ FcupIa) xr.ia) ≫ s.ι.app xr.a
  ι.naturality x y f:= by
    let fr := uc.repH f
    simp
    rw [colimColimIndep uc.iaSubC FcupIa uc.repLifting s (uc.repO y) (repHtoCd uc.iaSubC f fr)]
    rw [colimColimIndep uc.iaSubC FcupIa uc.repLifting s (uc.repO x) (repHtoD uc.iaSubC f fr)]

    suffices FcupIa.map f ≫ FcupIa.map fr.repCoDom.inv ≫ colimit.ι (uc.iaSubC.i fr.a ⋙ FcupIa) fr.iaCoDom ≫ s.ι.app fr.a = FcupIa.map fr.repDom.inv ≫ colimit.ι (uc.iaSubC.i fr.a ⋙ FcupIa) fr.iaDom ≫ s.ι.app fr.a by simpa

    -- ce serait cool d'avoir forceColimW qui s'occupe de ça mais on verra plus tard
    rw [← colimit.w ((uc.iaSubC.i fr.a ⋙ FcupIa)) fr.hom, ← Category.assoc]
    slice_lhs 1 1 => rw [← fr.rep]
    simp

/-
include repLifting
@[simp]
theorem colimColimIndep {x : C}  (r s : repObj iaSubC x) : FcupIa.map r.rep.inv ≫ colimit.ι ((F iaSubC FcupIa).i r.a) r.ia ≫ colimit.ι (colimFia iaSubC FcupIa ) r.a = FcupIa.map s.rep.inv ≫ colimit.ι ((F iaSubC FcupIa).i s.a) s.ia ≫ colimit.ι (colimFia iaSubC FcupIa ) s.a := by
  exact machin6 iaSubC FcupIa repLifting (colimit.cocone (colimFia iaSubC FcupIa)) r s
-/

attribute [local simp] F
/-- For any a the cocone structure over Fia of a cocone over FcupIa-/
@[simps]
def fCupIaCoconeToFiaCocone (s : Cocone FcupIa) : Cocone ((F iaSubC FcupIa).i a) where
  pt := s.pt
  ι.app x := s.ι.app ((iaSubC.i a).obj x)

attribute [local simp] F
set_option backward.isDefEq.respectTransparency false in
/-- The cocone structure  over lim FIa of a cocone over FcupIa with the same point-/
@[simps]
def fCupIaCoconeToColimFiaCocone (s : Cocone FcupIa ) : Cocone (colimFia iaSubC FcupIa) where
  pt := s.pt
  ι.app a := colimit.desc _ (fCupIaCoconeToFiaCocone iaSubC FcupIa a s)

attribute [local simp] F
set_option backward.isDefEq.respectTransparency false in
/-- The evidence that the colimit of colimit is a colimit over the "union of indexes"-/
@[simps]
def colimColimIsColim (uc: unionCat C i) (s : Cocone (colimFia uc.iaSubC FcupIa)) (hs : IsColimit s) : IsColimit (colimColimFiaCoconeFcupIa (i := i) FcupIa uc s) where
  desc t := hs.desc (fCupIaCoconeToColimFiaCocone uc.iaSubC FcupIa t)

  uniq t (m : s.pt ⟶ t.pt) hm := by
    apply hs.uniq (fCupIaCoconeToColimFiaCocone uc.iaSubC FcupIa t)
    intro a

    apply colimit.hom_ext
    intro x

    suffices colimit.ι ((F uc.iaSubC FcupIa).i a) x ≫ s.ι.app a ≫ m = t.ι.app ((uc.iaSubC.i a).obj x) by simpa

    rw [← hm _]


    repeat rw [← Category.assoc]
    apply eq_whisker

    suffices colimit.ι (uc.iaSubC.i a ⋙ FcupIa) x ≫ s.ι.app a = FcupIa.map (uc.repO ((uc.iaSubC.i a).obj x)).rep.inv ≫ colimit.ι (uc.iaSubC.i (uc.repO ((uc.iaSubC.i a).obj x)).a ⋙ FcupIa) (uc.repO ((uc.iaSubC.i a).obj x)).ia ≫ s.ι.app (uc.repO ((uc.iaSubC.i a).obj x)).a by simpa [F]

    rw [← colimColimIndep uc.iaSubC FcupIa uc.repLifting s (repCanO uc.iaSubC a x) (uc.repO ((uc.iaSubC.i a).obj x))]
    simp


variable [HasColimitsOfSize.{v2, u2} D]

set_option backward.isDefEq.respectTransparency false in
/-- The evidence that the colimit over the "union of indexes" is the colimit of the colimit-/
@[simps]
def colimIsColimColim (uc: unionCat C i) ( s : Cocone FcupIa) (hs : IsColimit s): IsColimit (fCupIaCoconeToColimFiaCocone uc.iaSubC FcupIa s) where

  desc t  := by
    exact hs.desc (by --truc bizzare ici
      apply colimColimFiaCoconeFcupIa _ uc
      exact t)
  fac t a := by
    apply colimit.hom_ext
    intro x
    suffices FcupIa.map (uc.repO ((uc.iaSubC.i a).obj x)).rep.inv ≫
    colimit.ι (uc.iaSubC.i (uc.repO ((uc.iaSubC.i a).obj x)).a ⋙ FcupIa) (uc.repO ((uc.iaSubC.i a).obj x)).ia ≫
      t.ι.app (uc.repO ((uc.iaSubC.i a).obj x)).a =
  colimit.ι ((F uc.iaSubC FcupIa).i a) x ≫ t.ι.app a by simpa

    rw [ ← colimColimIndep uc.iaSubC FcupIa uc.repLifting t (repCanO uc.iaSubC a _) (uc.repO ((uc.iaSubC.i a).obj _))]
    simp [F]
  uniq t (m : s.pt ⟶ t.pt) hm := by
    let c : Cocone FcupIa := by
      --truc bizzare ici
        apply colimColimFiaCoconeFcupIa  (uc := uc)
        exact t
    apply  hs.uniq c
    intro
    simp [ ← hm _, F, c]




end




end CategoryTheory.Limits
