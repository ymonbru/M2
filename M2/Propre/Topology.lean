import Mathlib.Topology.Sets.Compacts
import Mathlib.CategoryTheory.Filtered.Final

universe w v u

open Topology CategoryTheory TopologicalSpace Opposite Limits

#check Monotone.final_functor_iff
-- to put with Monotone.final_functor_iff
-- c'est la même preuve, donc peut être qu'on peut l'avoir avec dual?
theorem Monotone.initial_functor_iff {J₁ J₂ : Type*} [Preorder J₁] [Preorder J₂] [IsCodirectedOrder J₁] {f : J₁ → J₂} (hf : Monotone f) : hf.functor.Initial ↔ ( ∀ j₁,∃ j₂, f j₂ ≤ j₁) := by
  rw [Functor.initial_iff_of_isCofiltered]
  constructor
  · rintro ⟨h, _⟩ j₂
    obtain ⟨j₁, ⟨φ⟩⟩ := h j₂
    exact ⟨j₁,leOfHom φ⟩
  · intro h
    constructor
    · intro j₂
      obtain ⟨j₁, h₁⟩ := h j₂
      exact ⟨j₁, ⟨homOfLE h₁⟩⟩
    · intro _ c _ _
      exact ⟨ c, 𝟙 _, rfl⟩

variable {X : Type w} [TopologicalSpace X] {A : Type u} [Category.{v} A]

namespace TopologicalSpace.Compacts

/-- The compacts neigbourhoods of a compact.-/
def compactNhds (K : Compacts X) : Set (Compacts X) :=
  setOf (fun K' ↦ ∀ (x : K), K'.carrier ∈ 𝓝 x.val)

lemma subset_of_mem_compactNhds {K K' : Compacts X} (h : K' ∈ K.compactNhds) : K.carrier ⊆ K'.carrier := fun x hx ↦ mem_of_mem_nhds (h ⟨x, hx⟩)

lemma exists_open_nhds_sub_compact_nhds {K : Compacts X} (L : K.compactNhds) : ∃ U : Opens X, K.carrier ⊆ U.carrier ∧ U.carrier ⊆ L.1.carrier := by
  obtain ⟨U, KsubU, openU, UsubL⟩ := exists_open_set_nhds (fun x hx ↦ L.2 ⟨x, hx⟩)
  exact ⟨⟨U, openU⟩, KsubU, UsubL⟩

/-- The set of opens neighbourhood of a compact subset.-/
def openNhds (K : Compacts X) : Set (Opens X) := setOf (fun U ↦ K.carrier ⊆ U.carrier)

instance : Bot (⊥ : Compacts X).openNhds := ⟨⊥, fun _ h => h⟩

instance : IsInitial (⊥ : (⊥ : Compacts X).openNhds ) := by
  apply IsInitial.ofUniqueHom
  · intro _ _
    apply eq_of_comp_right_eq
    intro _ _
    rfl
  · intro
    apply homOfLE
    intro _ hx
    rcases hx

/-- The opens neighbourhood of a compact subset that are relatively compact.-/
def openRcNhds (K : Compacts X) : Set (Opens X) :=
  setOf (fun U ↦ IsCompact (closure U.carrier) ∧ K.carrier ⊆ U.carrier)

lemma subset_of_mem_openRcNhds {K : Compacts X} {U : Opens X} (h : U ∈ K.openRcNhds) : K.carrier ⊆ U.carrier :=
  fun _ hx => h.right hx

lemma compactclosure_of_mem_openRcNhds {K : Compacts X} {U : Opens X} (h : U ∈ K.openRcNhds) : IsCompact (closure U.carrier) := h.left

lemma is_compactNhds_of_isopenRcNhds {K : Compacts X} {U : Opens X} (h : U ∈ K.openRcNhds) : ⟨closure U.carrier, compactclosure_of_mem_openRcNhds h⟩ ∈ K.compactNhds := by
  intro
  apply Filter.sets_of_superset
  · apply IsOpen.mem_nhds
    · exact U.is_open'
    · exact Compacts.subset_of_mem_openRcNhds h ( Subtype.coe_prop _)
  · exact subset_closure

/-- The converting map from relatively compact opens neighbourhood of a compact subset to its opens neighbourhood-/
def oRcNhds_to_openNhds (K : Compacts X) : K.openRcNhds → K.openNhds := fun U => ⟨_, U.property.2⟩

lemma mono_oRcNhds_to_openNhds (K : Compacts X) : Monotone K.oRcNhds_to_openNhds := fun _ _ h => h

def oRcNhds_to_compactNhds (K : Compacts X) : K.openRcNhds → K.compactNhds := fun U => ⟨_,is_compactNhds_of_isopenRcNhds (Subtype.coe_prop U)⟩

lemma mono_oRcNhds_to_compactNhds (K : Compacts X) : Monotone K.oRcNhds_to_compactNhds := fun _ _ h => closure_mono h

variable [T2Space X] in
instance (K : Compacts X): IsCodirectedOrder  K.openRcNhds where
  directed U1 U2 := by
    use ⟨U1 ⊓ U2, by
      constructor
      apply IsCompact.of_isClosed_subset
      · apply IsCompact.inter
        apply compactclosure_of_mem_openRcNhds
        · exact Subtype.coe_prop U1
        · exact compactclosure_of_mem_openRcNhds U2.coe_prop
      · exact isClosed_closure
      · apply closure_inter_subset_inter_closure
      apply le_inf
      · exact subset_of_mem_openRcNhds (Subtype.coe_prop U1)
      · exact subset_of_mem_openRcNhds (Subtype.coe_prop U2)⟩
    use Subtype.coe_le_coe.mp  inf_le_left
    use Subtype.coe_le_coe.mp  inf_le_right

instance {K : Compacts X} [T2Space X] [LocallyCompactSpace X]: K.mono_oRcNhds_to_openNhds.functor.Initial := by
  apply (Monotone.initial_functor_iff _).2
  intro U
  obtain ⟨L, h1, h2, h3⟩ := exists_compact_between K.isCompact U.val.isOpen U.property
  use ⟨⟨interior L, isOpen_interior⟩, ⟨IsCompact.of_isClosed_subset h1 isClosed_closure (closure_minimal interior_subset (IsCompact.isClosed h1)), h2⟩⟩
  apply Set.Subset.trans interior_subset h3

instance {K : Compacts X} [T2Space X] : K.mono_oRcNhds_to_compactNhds.functor.Initial := by
  apply (Monotone.initial_functor_iff _).2
  intro L
  obtain ⟨U, h1, h2⟩ := exists_open_nhds_sub_compact_nhds L
  have h3 : closure U.carrier ⊆ L.1.carrier := (IsClosed.closure_subset_iff (IsCompact.isClosed L.1.isCompact') ).2 h2
  exact ⟨⟨U, ⟨ IsCompact.of_isClosed_subset L.1.isCompact' isClosed_closure h3, h1⟩⟩, h3⟩
end TopologicalSpace.Compacts

namespace TopologicalSpace.Opens

/-- The set of compacts inside an open subset.-/
def compactInsd (U : Opens X) : Set (Compacts X) := setOf (fun K ↦ K.carrier ⊆ U.carrier)

/-If K is a compact subset insde an open subset U, then U has a structure of open neighbourhood of K.-/
def toOpenNhds {U : Opens X } (K : U.compactInsd) : (K.val).openNhds := ⟨U, K.property⟩

/-- If U is a open subset included in a open subset V then there is a map sending compacts inside U to the ones inside V.-/
def baseChangeCompactInsd {U V : Opens X} (h : U ⟶ V) : U.compactInsd → V.compactInsd := fun ⟨K,hK⟩ => ⟨K, fun _ hx => by
  apply Set.mem_of_subset_of_mem (leOfHom h) (hK hx)⟩

lemma monoBaseChangeCompactInsd {U V : Opens X} (h : U ⟶ V) : Monotone <| baseChangeCompactInsd h := fun  _ _ hKL _ hx => SetLike.mem_coe.mpr (hKL hx)

end TopologicalSpace.Opens

namespace TopologicalSpace.Compacts

/-- If U is an open neighbourhood of K, then K has a structure of compact insde U.-/
def toCompactInsd {K : Compacts X} (U : K.openNhds) : (U.val).compactInsd := ⟨K, U.property⟩

/-- If K is a compact subset included in a compact subset L then there is a map sending open neighbourhoods of L to the ones of K.-/
def baseChangeOpenNhds {K L : Compacts X} (h : K ⟶ L) : L.openNhds → K.openNhds := fun ⟨U,hU⟩ => ⟨U, fun _ hx => Set.mem_of_subset_of_mem hU (leOfHom h hx)⟩

lemma monoBaseChangeOpenNhds {K L : Compacts X} (h : K ⟶ L) : Monotone <| baseChangeOpenNhds h := fun  _ _ hUV _ hx => SetLike.mem_coe.mpr (hUV hx)

@[simp]
lemma baseChangeOpenNhds_comp {K L M : Compacts X} (h : K ⟶ L) (k : L ⟶ M) (U : M.openNhds) : baseChangeOpenNhds (h ≫ k) U = baseChangeOpenNhds h (baseChangeOpenNhds k U) := by rfl

end TopologicalSpace.Compacts
