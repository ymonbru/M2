import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.Topology.Sets.Compacts
import Mathlib.Topology.Sets.Opens

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite

variable {X} [TopologicalSpace X]

noncomputable section
variable (K : Compacts X)
variable (P : Opens X → Prop)-- true for the usual alpha and IsCompact (closure U.carrier) for the relatively compact version

/--The property of containing K and satisfying P-/
def KsubU : Set (Opens X) := fun (U:Opens _) => (K.carrier ⊆ U) ∧ P U

/--The full subcategory induced by the property KsubU-/
def KsubU_cat : Type := FullSubcategory (KsubU K P)

/-instance : SetLike (KsubU_cat K P) X where
  coe U:= U.obj.carrier

  coe_injective':= fun ⟨_ , _ ⟩ ⟨_, _⟩ h => by
    apply FullSubcategory.ext
    simp at h
    exact h-/

instance : Category (KsubU_cat K P) := FullSubcategory.category (KsubU K P)

variable {P : Opens X → Prop } (axiomP : ∀ U1 U2, P U1 → P U2 → P (U1 ⊓ U2))
include axiomP

/-- U1 ⊓ U2 as an element of (KsubU_cat K P)ᵒᵖ-/
@[simps]
def InfKsubU (U1 U2 : KsubU_cat K P) : (KsubU_cat K P) := ⟨( U1.obj ⊓ U2.obj), ⟨le_inf U1.property.1 U2.property.1, axiomP _ _ U1.property.2 U2.property.2⟩ ⟩

/-- The morphisme U1 ⟶ U1 ⊓ U2 for elements of (KsubU_cat K P)ᵒᵖ-/
def InfInLeft (U1 U2 : KsubU_cat K P): (InfKsubU K axiomP U1 U2) ⟶ U1:= homOfLE (by simp)

/-- The morphisme U2 ⟶ U1 ⊓ U2 for elements of (KsubU_cat K P)ᵒᵖ-/
def InfInRight (U1 U2 : KsubU_cat K P ): (InfKsubU K axiomP U1 U2) ⟶ U2 := homOfLE (by simp)

include axiomP
--Implicit argument are an issue for infering the instance
/-- The evidence that the category (KsubU_cat K P) is cofiltered-/
lemma IsCofilteredKsubU: IsCofilteredOrEmpty (KsubU_cat K P) where
  cone_objs U1 U2 := by
    use InfKsubU K axiomP U1 U2
    use InfInLeft K axiomP U1 U2
    use InfInRight K axiomP U1 U2
  cone_maps U1 U2 _ _:= by
    use InfKsubU K axiomP U1 U2
    use InfInLeft K axiomP U1 U2
    rfl

end

section

variable (X) [TopologicalSpace X] [T2Space X]
variable (K : Compacts X)

/-- the condition of being relatively compact-/
def relcCond : Opens X → Prop := fun (U:Opens X) => IsCompact (closure (U:Set X))

lemma axiomPrc : ∀ (U₁ U₂ : Opens X), relcCond X U₁ → relcCond X U₂ → relcCond X (U₁ ⊓  U₂):= by
  intro U1 U2 h1 h2
  apply IsCompact.of_isClosed_subset
  · exact IsCompact.inter h1 h2
  · exact isClosed_closure
  · rw [ Opens.coe_inf]
    apply closure_inter_subset_inter_closure

def RelCN_cat : Type := (KsubU_cat K (relcCond _))

instance : Category (RelCN_cat X K) := instCategoryKsubU_cat K (relcCond X)
