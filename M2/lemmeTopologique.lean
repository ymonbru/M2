import Mathlib
import M2.KsubU

open Topology Set
open TopologicalSpace Compacts

/-lemma subset_compl_image_compl {α β : Type*} {u : Set α} {v : Set β} {f : α → β} :
    v ⊆ (f '' uᶜ)ᶜ ↔ f ⁻¹' v ⊆ u := by
  rw [subset_compl_comm, image_subset_iff, preimage_compl, compl_subset_compl]-/

universe w

variable {X Y : Type w } [TopologicalSpace X] [TopologicalSpace Y]

variable {f : X → Y} (closed_f : IsClosedMap f)

variable (K : Compacts Y) (L : Set X) (hKL : f ⁻¹' K ⊆ interior L)

include closed_f
lemma IsClosedMap.isOpen_kernImage {u : Set X} (hu : IsOpen u) :
    IsOpen (kernImage f u) := by
  rw [kernImage_eq_compl]
  exact (closed_f _ hu.isClosed_compl).isOpen_compl

variable [LocallyCompactSpace Y]

include closed_f hKL
lemma existsIntermedFrepKAndL :  Nonempty ({ K' // IsCompact K' ∧ K.carrier ⊆ interior K' ∧ f ⁻¹' K' ⊆ L }):=
  let ⟨K', hK', hKK', hK'L⟩ := exists_compact_between K.isCompact' (closed_f.isOpen_kernImage isOpen_interior) ( subset_kernImage_iff.2 hKL)
  ⟨K', hK', hKK', Set.Subset.trans (subset_kernImage_iff.1 hK'L) interior_subset⟩

/-- a Compact K' such that K ⊆⊆  and such that f⁻¹ K' ⊆ L-/
@[simps]
def existsIntermedFrepKAndLCompact : supSupK_cat K where
  obj := by
    let ⟨K', hK'⟩ := Classical.choice (existsIntermedFrepKAndL closed_f K L hKL)

    exact ⟨K', hK'.1⟩
  property := by
    let ⟨K', hK'⟩ := Classical.choice (existsIntermedFrepKAndL closed_f K L hKL)
    use ⟨interior K', isOpen_interior ⟩

    constructor
    · exact hK'.2.1
    · simp [interior_subset]

/-- The specification of existsIntermedFrepKAndLCompact-/
def existsIntermedFrepKAndLSpec : f ⁻¹' ( existsIntermedFrepKAndLCompact closed_f K L hKL).obj.carrier ⊆ L := (Classical.choice (existsIntermedFrepKAndL closed_f K L hKL)).2.2.2

/-- an open  U such that K ⊆ U  and such that f⁻¹ U ⊆ L-/
@[simps]
def existsIntermedFrepKAndLOpen : KsubU_cat K trueCond where
  obj := by
    let ⟨K', hK'⟩ := Classical.choice (existsIntermedFrepKAndL closed_f K L hKL)

    exact ⟨interior K',by

      sorry ⟩
  property := by
    let ⟨K', hK'⟩ := Classical.choice (existsIntermedFrepKAndL closed_f K L hKL)
    use ⟨interior K', isOpen_interior ⟩

    constructor
    · exact hK'.2.1
    · simp [interior_subset]
