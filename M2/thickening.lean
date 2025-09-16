import Mathlib
import M2.Suffices
import Mathlib.Topology.UniformSpace.Defs

def thickening (A : Set β) (V : Set (β × β)) : Set β := (⋃ x ∈ A, UniformSpace.ball x V)

lemma thickening_mem_iff (A : Set β) (V : Set (β × β)) (x : β) : x ∈ thickening A V ↔ ∃ y ∈ A, x ∈ UniformSpace.ball y V := by
  unfold thickening
  simp

lemma thickening_cup (A B : Set β) (V : Set (β × β)) : (thickening A V) ∪ (thickening B V) = (thickening (A ∪ B) V) := by
  apply Set.ext
  intro x
  constructor
  · intro h
    apply (thickening_mem_iff _ _ _).2
    rcases (Set.mem_union x (thickening A V)  (thickening B V)).1 h with hA | hB

    rcases (thickening_mem_iff _ _ _).1 hA with ⟨y, hy⟩
    use y
    constructor
    · left
      exact hy.1
    · exact hy.2

    rcases (thickening_mem_iff _ _ _).1 hB with ⟨y, hy⟩
    use y
    constructor
    · right
      exact hy.1
    · exact hy.2
  ·
    intro h
    rcases (thickening_mem_iff _ _ _).1 h with ⟨y, hy⟩
    rcases hy.1 with hA| hB
    · left
      apply (thickening_mem_iff _ _ _).2
      use y
      constructor
      · exact hA
      · exact hy.2
    · right
      apply (thickening_mem_iff _ _ _).2
      use y
      constructor
      · exact hB
      · exact hy.2

lemma thickening_montonus (A B : Set β) (h : A ⊆ B ) (V : Set (β × β)) : thickening A V ⊆ thickening B V := by
  intro x hx
  apply (thickening_mem_iff _ _ _).2
  rcases (thickening_mem_iff _ _ _).1 hx with ⟨y, hy⟩
  use y
  constructor
  · apply h
    exact hy.1
  · exact hy.2

lemma thickening_open (A : Set β) (V : Set (β × β)) [UniformSpace β ] (hV : IsOpen V) : IsOpen (thickening A V) := by
  apply isOpen_biUnion
  intro _ _
  apply UniformSpace.isOpen_ball
  assumption
