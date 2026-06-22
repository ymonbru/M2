import Mathlib
import M2.Propre.colimit

open Topology TopologicalSpace Set

section
variable {X} [TopologicalSpace X] [T2Space X] --[LocallyCompactSpace X]

lemma closure_of_inter_is_compact (K : Compacts X) (A B : Set X ) (h : A ⊆ K) : IsCompact (closure (A ∩ B)) := by
  apply IsCompact.closure_of_subset (K := K)
  exact K.isCompact
  apply Set.Subset.trans _ h
  exact inter_subset_left
end

section
variable {X Y} [TopologicalSpace X] [TopologicalSpace Y]

open CategoryTheory.Limits

#check colimitLimitIso

lemma int_comm_inter_V2 (A B : Set X) : interior (A ∩ B) = interior A ∩ interior B := by
  apply colimitLimitIso

lemma int_comm_prod_V (A : Set X) (B : Set Y) : interior (A ×ˢ B) = (interior A) ×ˢ (interior B) := by
  apply colimitLimitIso








lemma int_comm_inter (A B : Set X) : interior (A ∩ B) = interior A ∩ interior B := by
  exact interior_inter

lemma int_comm_prod (A : Set X) (B : Set Y) : interior (A ×ˢ B) = (interior A) ×ˢ (interior B) := by
  exact interior_prod_eq A B


















/-apply IsCompact.closure_of_subset (K := K)
  exact K.isCompact
  apply Set.Subset.trans _ h
  apply inf_le_left-/

end
/-noncomputable section
open CategoryTheory CategoryTheory.Limits
#check IsColimitCoconeOfLimF

variable {X Y} [TopologicalSpace X] [TopologicalSpace Y]

def Set.openInsd (A : Set X) : Set (Opens X) := setOf (fun U ↦ U.carrier ⊆ A)

def Dfun (A : Set X) : (A.openInsd ) →  Set X := fun U => U.val

lemma Dmono (A : Set X) : Monotone (Dfun A) := fun _ _ h => le_iff_subset.mpr h

def Da (A : Set X) : (A.openInsd ) ⥤  Set X := (Dmono A).functor

variable (A B : Set X)

def D : Discrete WalkingPair ⥤ (A.openInsd × B.openInsd) ⥤ Set X := pair (CategoryTheory.Prod.fst _ _ ⋙ Da A) (CategoryTheory.Prod.snd _ _ ⋙ Da B)

variable (Z: Type ) [Preorder Z]

instance : ConcreteCategory Z := by sorry

instance :  PreservesLimitsOfShape (Discrete WalkingPair) (forget (Set X)) := by sorry

instance : PreservesLimitsOfShape (Discrete WalkingPair) (colim : ((A.openInsd × B.openInsd) ⥤ Set X) ⥤ _) := by
  apply CategoryTheory.Limits.filtered_colim_preservesFiniteLimits
  sorry


#check IsColimitCoconeOfLimF (F := D A B)

end-/
