import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.Topology.Sets.Compacts
import Mathlib.Topology.Sets.Opens
--import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Filtered.Final

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite

noncomputable section
variable {X} [TopologicalSpace X]
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

/-- The evidence that the category (KsubU_cat K P) is cofiltered-/
lemma IsCofilteredKsubU : IsCofilteredOrEmpty (KsubU_cat K P) where
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
variable {X} [TopologicalSpace X] [T2Space X]
variable (K : Compacts X)

/-- the condition of being relatively compact-/
def relcCond : Opens X → Prop := fun (U:Opens X) => IsCompact (closure (U:Set X))

lemma axiomPrc : ∀ (U₁ U₂ : Opens X), relcCond U₁ → relcCond U₂ → relcCond (U₁ ⊓  U₂):= by
  intro U1 U2 h1 h2
  apply IsCompact.of_isClosed_subset
  · exact IsCompact.inter h1 h2
  · exact isClosed_closure
  · rw [ Opens.coe_inf]
    apply closure_inter_subset_inter_closure

def RelCN_cat : Type := (KsubU_cat K (relcCond))

instance : Category (RelCN_cat K) := instCategoryKsubU_cat K (relcCond)

instance : IsCofilteredOrEmpty (RelCN_cat K) := by
    apply IsCofilteredKsubU
    apply axiomPrc

variable [LocallyCompactSpace X] -- the locally compact is here for the non emptyness of RelCN_cat

instance : Nonempty (RelCN_cat K) := by
  have : IsOpen (⊤ : Set X)  := isOpen_univ
  have this2 : K.carrier ⊆ ⊤ := by
    intro _ _
    trivial
  rcases (exists_compact_between K.isCompact this this2 ) with ⟨L,hL⟩
  use ⟨interior L,@isOpen_interior X L _⟩
  constructor
  · exact hL.2.1
  · apply IsCompact.of_isClosed_subset hL.1 (isClosed_closure )
    intro a ha
    apply ha
    constructor
    · exact IsCompact.isClosed hL.1
    · apply interior_subset

end

section
variable {X} [TopologicalSpace X] [T2Space X]
variable (K : Compacts X)

def supSupK : Set (Compacts X) := fun (L : Compacts _) => (∃ (U: Opens _), (K.carrier ⊆ U.carrier) ∧ (U.carrier ⊆ L.carrier))

def supSupK_cat : Type := FullSubcategory (supSupK K )

omit [T2Space X] in
lemma supSupKtoSupK (L : supSupK_cat K) : K.carrier ⊆ L.obj.carrier := by
  rcases L.property with ⟨U, hU1, hU2⟩
  exact hU1.trans hU2


instance : Category (supSupK_cat K ) := FullSubcategory.category (supSupK K)

instance : IsCofilteredOrEmpty (supSupK_cat K) := by sorry

variable [LocallyCompactSpace X] -- the locally compact is here for the non emptyness of RelCN_cat

instance : Nonempty (supSupK_cat K) := by sorry

#check (fullSubcategoryInclusion (supSupK K) : (supSupK_cat K) ⥤ (Compacts X))
@[simp]
def closureFuncK : RelCN_cat K ⥤ supSupK_cat K where
  obj U := ⟨⟨closure U.obj, U.property.2⟩, by
    use U.obj
    constructor
    exact U.property.1
    exact subset_closure ⟩
  map _ :=  homOfLE <| closure_mono <| leOfHom _

lemma containClosure (U : Opens X) (L : Compacts X) (h : U.carrier ⊆ L.carrier) : closure U.carrier ⊆ L.carrier := by
  apply closure_minimal h
  apply IsCompact.isClosed
  exact L.isCompact'

instance closureFuncIsInitial : Functor.Initial (closureFuncK K) := by
  apply (Functor.initial_iff_of_isCofiltered _).2
  constructor
  intro L
  rcases L.property with ⟨U, hU1, hU2⟩
  use ⟨U, by
    constructor
    exact hU1
    apply IsCompact.of_isClosed_subset
    exact L.obj.isCompact'
    exact isClosed_closure
    apply containClosure
    exact hU2⟩-- probablement utile de le factoriser non?

  apply Nonempty.intro
  apply homOfLE
  apply containClosure
  exact hU2

  intro _ U _ _
  use U
  use 𝟙 _
  rfl
