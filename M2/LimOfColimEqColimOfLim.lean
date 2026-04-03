import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit

open CategoryTheory Limits

universe u1 v1 u2 v2 u3 v3 u4 v4

section

variable {C : Type u1} [Category.{v1} C]
variable {J : Type u2} [Category.{v2} J]
variable {K : Type u3} [Category.{v3} K]
variable [HasLimitsOfShape J C] [HasColimitsOfShape K C]
variable [PreservesLimitsOfShape J (colim : (K ⥤ C) ⥤ _)]


variable {F : J ⥤ K ⥤ C}

variable (limF : Cone F) (colimF : Cocone F.flip) (colimLimF : Cocone limF.pt) (limColimF : Cone colimF.pt)

variable (hLimF : IsLimit limF) (hColimF : IsColimit colimF) (hColimLimF : IsColimit colimLimF) (hLimColimF : IsLimit limColimF)

/-- Translate an isomorphism of cones into an isomorphism between the undeling points-/
@[simp]
def IsoConeToIsoPt {F : J ⥤ C} {s t : Cone F} (h : s ≅ t) : s.pt ≅ t.pt where
  hom := h.hom.hom
  inv := h.inv.hom

/-- Translate an isomorphism of cocones into an isomorphism between the undeling points-/
@[simp]
def IsoCoconeToIsoPt {F : J ⥤ C} {s t : Cocone F} (h : s ≅ t) : s.pt ≅ t.pt where
  hom := h.hom.hom
  inv := h.inv.hom

/-- The isomorphism between limcolim F and colimLimF for any cone and cocones.
It's composition of (colimitLimitIso F) and the canonicals isomorphisms-/
noncomputable def limColimFPtIsoColimLimFPt : limColimF.pt ≅ colimLimF.pt := (IsoConeToIsoPt (IsLimit.uniqueUpToIso hLimColimF (limit.isLimit colimF.pt)) ≪≫ HasLimit.isoOfNatIso ( IsoCoconeToIsoPt (IsColimit.uniqueUpToIso hColimF (colimit.isColimit F.flip))) ≪≫ (colimitLimitIso F).symm ≪≫ HasColimit.isoOfNatIso ( IsoConeToIsoPt (IsLimit.uniqueUpToIso hLimF (limit.isLimit F))).symm ≪≫ IsoCoconeToIsoPt (IsColimit.uniqueUpToIso hColimLimF (colimit.isColimit limF.pt)).symm)

/-- The cone structure over coliLimF.pt -/
@[simp]
noncomputable def ConeOverColimLimF : Cone colimF.pt := Cone.extend _ (limColimFPtIsoColimLimFPt limF colimF colimLimF limColimF hLimF hColimF hColimLimF hLimColimF).inv

noncomputable def IsLimitConeOfColimF : IsLimit (ConeOverColimLimF limF colimF colimLimF limColimF hLimF hColimF hColimLimF hLimColimF) := IsLimit.extendIso _ hLimColimF

--tout ce qui suit c'est poubelle normalement: je le garde pour que la version pas propre continue à compiler

set_option backward.isDefEq.respectTransparency false in
/-- For any j, the natural transformation from F(j) to colimF.pt(j)-/
@[simps]
def FjToColimFj (j : J) : F.obj j ⟶ (Functor.const K).obj (colimF.pt.obj j) where
  app x := (colimF.ι.app x).app j
  naturality x y f := by

    have : (F.obj j).map f ≫ (colimF.ι.app y).app j = (F.flip.map f ≫ colimF.ι.app y).app j := by
      rfl
    rw [this, colimF.ι.naturality]
    rfl

/--for any j, the structure of Cocone limF.pt over colimF.pt.obj j-/
@[simps]
def CoconeOverColimFj (j : J) : Cocone limF.pt := ⟨ colimF.pt.obj j, limF.π.app j ≫ ( FjToColimFj _ _ )⟩

set_option backward.isDefEq.respectTransparency false in
/-- The natural transformation involved in ConeOverColimLimF-/
@[simps]
def ConeOverColimLimFπ : (Functor.const J).obj colimLimF.pt ⟶ colimF.pt where
  app j := hColimLimF.desc (CoconeOverColimFj _ _ _)
  naturality i j f := by
    suffices hColimLimF.desc (CoconeOverColimFj _ _ _) ≫ colimF.pt.map f = hColimLimF.desc (CoconeOverColimFj _ _ _) by simp [this]
    apply hColimLimF.uniq (CoconeOverColimFj _ _ _)
    intro x
    suffices (limF.π.app i).app x ≫ (colimF.ι.app x).app i ≫ colimF.pt.map f = (limF.π.app j).app x ≫ (colimF.ι.app x).app j by simpa
    have : colimF.pt.map f = (((Functor.const K).obj colimF.pt).obj x).map f := by simp
    rw [this, ← (colimF.ι.app x).naturality ]

    suffices limF.π.app i ≫ F.map f = limF.π.app j by
      rw [← this, ← Category.assoc]
      rfl
    rw [ ← limF.π.naturality ]
    simp


/-- The cone structure over coliLimF.pt -/
@[simp]
def ConeOverColimLimF2 : Cone colimF.pt where
  pt := colimLimF.pt
  π := ConeOverColimLimFπ _ _ _ hColimLimF

set_option backward.isDefEq.respectTransparency false in
noncomputable def IsLimitConeOfColimF2 : IsLimit (ConeOverColimLimF2 _ colimF colimLimF (hColimLimF) ) where
  lift s := hLimColimF.lift s ≫ (limColimFPtIsoColimLimFPt _ _ _ _ hLimF hColimF hColimLimF hLimColimF).hom
  fac s j := by
    rw [ ← hLimColimF.fac s j, Category.assoc]
    apply whisker_eq
    suffices (ConeOverColimLimF2  limF colimF colimLimF hColimLimF).π.app j = (limColimFPtIsoColimLimFPt limF colimF colimLimF limColimF hLimF hColimF hColimLimF hLimColimF).inv ≫ limColimF.π.app j by
      rw [this]
      simp
    apply Eq.symm
    apply hColimLimF.uniq (CoconeOverColimFj limF colimF j)
    intro
    simp [limColimFPtIsoColimLimFPt]
  uniq s (m : s.pt ⟶ colimLimF.pt) hm := by
    rw [← hLimColimF.uniq s (m ≫ (limColimFPtIsoColimLimFPt _ _ _ _ hLimF hColimF hColimLimF hLimColimF).inv)]
    · simp
    · intro j
      rw [← hm j, Category.assoc]
      apply whisker_eq
      apply hColimLimF.uniq (CoconeOverColimFj limF colimF j)
      intro
      simp [limColimFPtIsoColimLimFPt]

end
