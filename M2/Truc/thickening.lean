import Mathlib

open TopologicalSpace TopologicalSpace.Compacts

variable {X :Type} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]

variable (K1 K2 U : Set X) (h1 : IsCompact K1) (h2: IsCompact K2) (hU : IsOpen U) (h : K1 ∩ K2 ⊆ U)

/- The type of small things-/
def Eps : Type := sorry

/- There is a way to compare two elements of Eps-/
instance : SemilatticeInf Eps := sorry

/- The operation of thickening-/
def thickening : Set X → Eps → Set X := sorry

lemma selfSubThickening (e : Eps ) (A : Set X) : A ⊆ thickening A e := sorry

/- A smaller thickening is included in a bigger one-/
lemma isMonotonusEpsThickening (e f : Eps) (h : e ≤ f) (A : Set X) : thickening A e ⊆ thickening A f := sorry

lemma isMonotonusSetThickening (e : Eps) (A B : Set X) ( h : A ⊆ B): thickening A e ⊆ thickening B e  := by sorry

lemma isMonotonusThickening (e f : Eps) (A B : Set X) (hE : e ≤ f) (hS : A ⊆ B) : thickening A e ⊆ thickening B f := by
  apply Set.Subset.trans
  apply isMonotonusSetThickening _ _ _ hS
  apply isMonotonusEpsThickening _ _ hE

lemma cupMonotonusthinckening (e : Eps) (A B : Set X) : thickening (A ∪ B) e ⊆ thickening A e ∪ thickening B e := sorry

/- A thickening is always open-/
lemma isOpenThickening (e : Eps) (A : Set X) : IsOpen <| thickening A e := sorry

/- In a T2 space one can draw a line between a compact and a close subset-/
lemma disjointThickenings (A B : Set X) (hD : Disjoint A B) (h1 : IsCompact A)  (h2 : IsClosed B) :  ∃ e : Eps, Disjoint (thickening A e) (thickening B e) := sorry

lemma compactInOpenThickening (K O : Set X) (hK : IsCompact K) (hO : IsOpen O) (h : K ⊆ O) : ∃ e : Eps, thickening K e ⊆ O := by
  let F := Oᶜ
  have hF : IsClosed F := isClosed_compl_iff.2 hO
  have : Disjoint K F := Set.disjoint_compl_right_iff_subset.2 h

  let e := (disjointThickenings K F this hK hF).choose
  let he : Disjoint (thickening K e) (thickening F e) := (disjointThickenings K F this hK hF).choose_spec

  have : Disjoint (thickening K e ) F := Disjoint.mono_right (selfSubThickening e F) he

  use e
  exact Set.disjoint_compl_right_iff_subset.1 this


/- The theorem i want to show-/
include h1 h2 hU h in
theorem Goal : ∃ V1 V2 : Set X, IsOpen V1 ∧ IsOpen V2 ∧ K1 ⊆ V1 ∧ K2 ⊆ V2 ∧ V1 ∩ V2 ⊆ U := by

  -- Let V be an open such that K1 ∩ K2 ⊆ V and e such that thickening V e ⊆ U
  -- It's possible in locally comapct spaces.
  let L := (exists_compact_between (IsCompact.inter h1 h2) hU h).choose
  let hL :  IsCompact L ∧ K1 ∩ K2 ⊆ interior L ∧ L ⊆ U:= (exists_compact_between (IsCompact.inter h1 h2) hU h).choose_spec

  let e1 : Eps := (compactInOpenThickening L U hL.1 hU hL.2.2).choose
  let he1 : thickening L e1 ⊆ U:= (compactInOpenThickening L U hL.1 hU hL.2.2).choose_spec

  let V : Set X := interior L
  have hV : IsOpen V := isOpen_interior

  have K12subV : K1 ∩ K2 ⊆ V := hL.2.1

  have VepsSubU : thickening V e1 ⊆ U := by
    apply Set.Subset.trans _
    exact he1
    apply isMonotonusSetThickening
    exact interior_subset

  -- Let A and B be the following disjoint compacts :
  let A := K1 \ V
  let B := K2 \ V

  have hA : IsCompact A := by
    refine IsCompact.diff ?_ ?_
    exact h1
    exact hV

  have hB : IsClosed B := by
    refine IsClosed.sdiff ?_ ?_
    apply IsCompact.isClosed
    exact h2
    exact hV

  have hAB : Disjoint A B := by
    apply Set.disjoint_iff.2
    intro x hx

    have : x ∉ V :=((Set.mem_diff _).1 hx.1).2
    apply this

    have : x ∈ K1 ∩ K2 := by
      constructor
      exact ((Set.mem_diff _).1 hx.1).1
      exact ((Set.mem_diff _).1 hx.2).1
    exact K12subV this

  -- let e2 be sucht thath the thickenings of A and B of length e2 are disjoint.
  let e2 : Eps := (disjointThickenings A B hAB hA hB).choose
  let he : Disjoint (thickening A e2) (thickening B e2):= (disjointThickenings A B hAB hA hB).choose_spec

  -- let e be the infimum of e1 and e2 wich will be the length of thickening to obtain V1 and V2
  let e := e1 ⊓ e2

  let V1 := thickening K1 e
  let V2 := thickening K2 e

  use V1
  use V2
  constructor
  · exact isOpenThickening e K1
  constructor
  · exact isOpenThickening e K2

  constructor
  · exact selfSubThickening e K1
  constructor
  · exact selfSubThickening e K2

  -- show by contradiction that V1 ∩ V1 ⊆ U, wich is the last step.
  · intro x hx
    by_contra hx2

    have : V1 ⊆ thickening A e ∪ thickening V e := by
      apply Set.Subset.trans
      apply isMonotonusSetThickening _ _ _ (Set.subset_diff_union K1 V)
      apply Set.Subset.trans
      apply cupMonotonusthinckening
      apply Set.union_subset_union_right
      rfl

    have : V2 ⊆ thickening B e ∪ thickening V e := by
      apply Set.Subset.trans
      apply isMonotonusSetThickening _ _ _ (Set.subset_diff_union K2 V)
      apply Set.Subset.trans
      apply cupMonotonusthinckening
      apply Set.union_subset_union_right
      rfl

    have  contra: V1 ∩ V2 ⊆ (thickening A e ∪ thickening V e) ∩ (thickening B e ∪ thickening V e) := by
      apply  Set.inter_subset_inter
      repeat assumption

    have : (thickening A e) ∩ (thickening B e) = ∅ :=  by
      apply Disjoint.eq_bot
      apply Disjoint.mono_right
      apply isMonotonusEpsThickening _ _ inf_le_right
      apply Disjoint.mono_left
      apply isMonotonusEpsThickening _ _ inf_le_right
      exact he

    have : (thickening A e ∪ thickening V e) ∩ (thickening B e ∪ thickening V e) ⊆ thickening V e := by
      rw [Set.inter_union_distrib_left, Set.union_inter_distrib_right,this]
      simp

    apply hx2
    apply VepsSubU
    apply isMonotonusEpsThickening _ _ inf_le_left
    apply this
    apply contra
    exact hx
