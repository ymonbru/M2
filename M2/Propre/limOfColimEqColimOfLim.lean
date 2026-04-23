import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit

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

end CategoryTheory.Limits
