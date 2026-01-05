import Mathlib.Order.CompleteLattice.MulticoequalizerDiagram
import Mathlib.Topology.Sets.Compacts
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
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

theorem initial_of_isCofilteredOrder {X : Type y} {Y : Type v} [Preorder X] [Preorder Y] [IsCodirectedOrder X] {f : X → Y} (hmf : Monotone f) (h : ∀ d,∃ c, f c ≤ d) : Functor.Initial hmf.functor := by
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

def openrelativelycompactNhds (K : Compacts X) : Set (Opens X) :=
  setOf (fun U ↦ IsCompact (closure U.carrier) ∧ K.carrier ⊆ U.carrier)

lemma subset_of_mem_openrelativelycompactNhds {K : Compacts X} {U : Opens X} (h : U ∈ K.openrelativelycompactNhds) : K.carrier ⊆ U.carrier :=
  fun _ hx => h.right hx

lemma compactclosure_of_mem_openrelativelycompactNhds {K : Compacts X} {U : Opens X} (h : U ∈ K.openrelativelycompactNhds) : IsCompact (closure U.carrier) := h.left

lemma is_compactNhds_of_isopenrelativelycompactNhds {K : Compacts X} {U : Opens X} (h : U ∈ K.openrelativelycompactNhds) : ⟨closure U.carrier,   compactclosure_of_mem_openrelativelycompactNhds h⟩ ∈ K.compactNhds := by
  intro
  apply Filter.sets_of_superset
  · apply IsOpen.mem_nhds
    · exact U.is_open'
    · apply Compacts.subset_of_mem_openrelativelycompactNhds h
      exact Subtype.coe_prop _
  · exact subset_closure

@[simps]
def orcNhds_to_compactNhds (K : Compacts X) : K.openrelativelycompactNhds → K.compactNhds := fun U => ⟨_,is_compactNhds_of_isopenrelativelycompactNhds (Subtype.coe_prop U)⟩

lemma mono_orcNhds_to_compactNhds (K : Compacts X) : Monotone K.orcNhds_to_compactNhds := fun _ _ h => closure_mono h

variable [T2Space X] in
instance (K : Compacts X): IsCodirectedOrder  K.openrelativelycompactNhds where
  directed U1 U2 := by
    use ⟨U1 ⊓ U2, by
      constructor
      apply IsCompact.of_isClosed_subset
      · apply IsCompact.inter
        apply compactclosure_of_mem_openrelativelycompactNhds
        exact Subtype.coe_prop U1
        apply compactclosure_of_mem_openrelativelycompactNhds
        exact Subtype.coe_prop U2
      · exact isClosed_closure
      · apply closure_inter_subset_inter_closure
      apply le_inf
      · exact subset_of_mem_openrelativelycompactNhds (Subtype.coe_prop U1)
      · exact subset_of_mem_openrelativelycompactNhds (Subtype.coe_prop U2)⟩
    use Subtype.coe_le_coe.mp  inf_le_left
    use Subtype.coe_le_coe.mp  inf_le_right


instance {K : Compacts X} [T2Space X]: Functor.Initial K.mono_orcNhds_to_compactNhds.functor := by
  apply Monotone.initial_of_isCofilteredOrder
  intro L
  obtain ⟨U, h1, h2⟩ := exists_open_nhds_sub_compact_nhds L
  have h3 : closure U.carrier ⊆ L.1.carrier := (IsClosed.closure_subset_iff (IsCompact.isClosed L.1.isCompact') ).2 h2

  use ⟨U, ⟨ IsCompact.of_isClosed_subset L.1.isCompact' isClosed_closure h3, h1⟩⟩
  exact h3

end TopologicalSpace.Compacts

variable (X A) in
abbrev KPresheaf := (Compacts X)ᵒᵖ ⥤ A

namespace KPresheaf

@[simps]
def coconeOfCompacts (P : KPresheaf X A) (K : Compacts X) :
    Cocone ((Subtype.mono_coe K.compactNhds).functor.op ⋙ P) where
  pt := P.obj (op K)
  ι.app K' := P.map (homOfLE (Compacts.subset_of_mem_compactNhds K'.unop.prop)).op
  ι.naturality _ _ _ := by
    dsimp
    rw [Category.comp_id, ← Functor.map_comp]
    rfl

#check Cocone.whisker K.mono_orcNhds_to_compactNhds.functor.op


variable [T2Space X]

structure IsKSheaf (P : KPresheaf X A) : Prop where
  nonempty_isTerminal : Nonempty (IsTerminal (P.obj (op ⊥)))
  isPullback {K₁ K₂ K₃ K₄ : Compacts X} (h : Lattice.BicartSq K₁ K₂ K₃ K₄) :
    IsPullback (P.map ((homOfLE h.le₃₄).op)) (P.map ((homOfLE h.le₂₄).op))
      (P.map ((homOfLE h.le₁₃).op)) (P.map ((homOfLE h.le₁₂).op))
  nonempty_isColimit_coconeOfCompacts (K : Compacts X) :
      Nonempty (IsColimit (P.coconeOfCompacts K))

end KPresheaf

variable [T2Space X]

variable (X A) in
structure KSheaf where
  val : KPresheaf X A
  cond : KPresheaf.IsKSheaf val

namespace Ksheaf

instance :  Category (KSheaf X A) := InducedCategory.category (·.val)
