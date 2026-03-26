import Mathlib.Topology.Sets.Compacts
import Mathlib.CategoryTheory.Filtered.Final

universe w v u

open Topology CategoryTheory TopologicalSpace Opposite Limits

namespace CategoryTheory

instance (E : Type u) [Preorder E] [IsCodirectedOrder E] : IsCofilteredOrEmpty E where
  cone_objs := by
    intro x y
    obtain ⟨w, h1, h2⟩ := exists_le_le x y
    exact ⟨w,homOfLE h1,homOfLE h2, True.intro⟩
  cone_maps := by
    intro x _ _ _
    use x
    use 𝟙 _
    rfl

end CategoryTheory

namespace Monotone
#check Monotone.final_functor_iff
--il y a Monotone.final_functor_iff mais pas celui la
theorem initial_functor_iff {X : Type u} {Y : Type v} [Preorder X] [Preorder Y] [IsCodirectedOrder X] {f : X → Y} (hmf : Monotone f) : hmf.functor.Initial ↔ ( ∀ d,∃ c, f c ≤ d) := by
  constructor
  · intro h d
    obtain ⟨c, ⟨i⟩⟩  := ((Functor.initial_iff_of_isCofiltered _).1 h).1 d
    exact ⟨c,leOfHom i⟩
  · intro h
    apply (Functor.initial_iff_of_isCofiltered _).2
    constructor
    · intro d
      obtain ⟨c,hc⟩ := h d
      exact ⟨c,Nonempty.intro <| homOfLE hc⟩
    · intro _ c _ _
      exact ⟨ c, 𝟙 c, rfl⟩
end Monotone


variable {X : Type w} [TopologicalSpace X] {A : Type u} [Category.{v} A]


namespace TopologicalSpace.Compacts

def compactNhds (K : Compacts X) : Set (Compacts X) :=
  setOf (fun K' ↦ ∀ (x : K), K'.carrier ∈ 𝓝 x.val)

lemma subset_of_mem_compactNhds {K K' : Compacts X} (h : K' ∈ K.compactNhds) : K.carrier ⊆ K'.carrier :=
  fun x hx ↦ mem_of_mem_nhds (h ⟨x, hx⟩)

lemma exists_open_nhds_sub_compact_nhds {K : Compacts X} (L : K.compactNhds) : ∃ U : Opens X, K.carrier ⊆ U.carrier ∧ U.carrier ⊆ L.1.carrier := by
  obtain ⟨U, KsubU, openU, UsubL⟩ := exists_open_set_nhds (fun x hx ↦ L.2 ⟨x, hx⟩)
  exact ⟨⟨U, openU⟩ , KsubU, UsubL⟩

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

def openRcNhds (K : Compacts X) : Set (Opens X) :=
  setOf (fun U ↦ IsCompact (closure U.carrier) ∧ K.carrier ⊆ U.carrier)

lemma subset_of_mem_openRcNhds {K : Compacts X} {U : Opens X} (h : U ∈ K.openRcNhds) : K.carrier ⊆ U.carrier :=
  fun _ hx => h.right hx

lemma compactclosure_of_mem_openRcNhds {K : Compacts X} {U : Opens X} (h : U ∈ K.openRcNhds) : IsCompact (closure U.carrier) := h.left

lemma is_compactNhds_of_isopenRcNhds {K : Compacts X} {U : Opens X} (h : U ∈ K.openRcNhds) : ⟨closure U.carrier,   compactclosure_of_mem_openRcNhds h⟩ ∈ K.compactNhds := by
  intro
  apply Filter.sets_of_superset
  · apply IsOpen.mem_nhds
    · exact U.is_open'
    · apply Compacts.subset_of_mem_openRcNhds h
      exact Subtype.coe_prop _
  · exact subset_closure

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
        exact Subtype.coe_prop U1
        apply compactclosure_of_mem_openRcNhds
        exact Subtype.coe_prop U2
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
  use ⟨⟨interior L, isOpen_interior⟩, ⟨IsCompact.of_isClosed_subset h1 isClosed_closure
          (closure_minimal interior_subset (IsCompact.isClosed h1)), h2⟩⟩
  apply Set.Subset.trans interior_subset h3

instance {K : Compacts X} [T2Space X] : K.mono_oRcNhds_to_compactNhds.functor.Initial := by
  apply (Monotone.initial_functor_iff _).2
  intro L
  obtain ⟨U, h1, h2⟩ := exists_open_nhds_sub_compact_nhds L
  have h3 : closure U.carrier ⊆ L.1.carrier := (IsClosed.closure_subset_iff (IsCompact.isClosed L.1.isCompact') ).2 h2
  use ⟨U, ⟨ IsCompact.of_isClosed_subset L.1.isCompact' isClosed_closure h3, h1⟩⟩
  exact h3

end TopologicalSpace.Compacts

namespace TopologicalSpace.Opens

def compactInsd (U : Opens X) : Set (Compacts X) := setOf (fun K ↦ K.carrier ⊆ U.carrier)

end TopologicalSpace.Opens

namespace  Subtype

def toOpenNhds {U : Opens X } (K : U.compactInsd) : (K.val).openNhds := ⟨U, K.property⟩

def toCompactInsd {K : Compacts X} (U : K.openNhds) : (U.val).compactInsd := ⟨K, U.property⟩

end Subtype

def Quiver.Hom.baseChangeOpenNhds {K L : Compacts X} (h : K ⟶ L) : L.openNhds → K.openNhds := fun ⟨U,hU⟩ => ⟨U, fun _ hx => Set.mem_of_subset_of_mem hU (leOfHom h hx)⟩

lemma monoBaseChangeOpenNhds {K L : Compacts X} (h : K ⟶ L) : Monotone <| h.baseChangeOpenNhds := fun  _ _ hUV _ hx => SetLike.mem_coe.mpr (hUV hx)

def Quiver.Hom.baseChangeCompactInsd {U V : Opens X} (h : U ⟶ V) : U.compactInsd → V.compactInsd := fun ⟨K,hK⟩ => ⟨K, fun _ hx => by
  apply Set.mem_of_subset_of_mem (leOfHom h) (hK hx)⟩

lemma monoBaseChangeCompactInsd {U V : Opens X} (h : U ⟶ V) : Monotone <| h.baseChangeCompactInsd := fun  _ _ hKL _ hx => SetLike.mem_coe.mpr (hKL hx)



#min_imports
