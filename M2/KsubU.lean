import M2.natTransWC
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.Topology.Sets.Compacts
import Mathlib.Topology.Sets.Opens
--import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Filtered.Final

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite

universe u v w

variable {X : Type u} [TopologicalSpace X]
variable (K : Compacts X)
variable {C : Type v} [Category.{w, v} C] (F : (Opens X)ᵒᵖ ⥤ C)
-- It's not usefull in most of the file but i want to declare it before P

noncomputable section

/-- The condition that is always true -/
@[simp]
def trueCond : Opens X → Prop:= λ _ => true

variable (P : Opens X → Prop := trueCond)-- true for the usual alpha and IsCompact (closure U.carrier) for the relatively compact version

/--The property of containing K and satisfying P-/
@[simp]
def KsubU : Set (Opens X) := fun (U:Opens _) => (K.carrier ⊆ U) ∧ P U

/--The full subcategory induced by the property KsubU-/
def KsubU_cat : Type u := ObjectProperty.FullSubcategory (KsubU K P)

/-instance : SetLike (KsubU_cat K P) X where
  coe U:= U.obj.carrier

  coe_injective':= fun ⟨_ , _ ⟩ ⟨_, _⟩ h => by
    apply FullSubcategory.ext
    simp at h
    exact h-/

instance : Category (KsubU_cat K P) := ObjectProperty.FullSubcategory.category (KsubU K P)

/-- The functor that sends opens that containt K2 to opens that contains K1-/
@[simps]
def K1subK2subU {K₁ K₂ : Compacts X} (f : K₁ ⟶ K₂): (KsubU_cat K₂ P) ⥤ (KsubU_cat K₁ P ) where
  obj W := (⟨W.obj,Set.Subset.trans (leOfHom f ) W.property.1
  , W.property.2⟩)
  map i := homOfLE (leOfHom i)

/-- The diagram obtained by restricting F to the category KsubU-/
@[simps!]
def FU : (KsubU_cat K P)ᵒᵖ ⥤ C := (ObjectProperty.ι (KsubU K P)).op.comp  F

variable {P : Opens X → Prop } (axiomP : ∀ U1 U2, P U1 → P U2 → P (U1 ⊓ U2))
include axiomP

/-- U1 ⊓ U2 as an element of (KsubU_cat K P)-/
@[simps]
def InfKsubU (U1 U2 : KsubU_cat K P) : (KsubU_cat K P) := ⟨( U1.obj ⊓ U2.obj), ⟨le_inf U1.property.1 U2.property.1, axiomP _ _ U1.property.2 U2.property.2⟩ ⟩

/- Quand il y a P Lean n'infère pas seul le inf, donc pas une si bonne idée...
instance : Min (KsubU_cat K) where
  min U1 U2 := ⟨( U1.obj ⊓ U2.obj), ⟨le_inf U1.property.1 U2.property.1, (by  rfl)⟩ ⟩

variable (U1 U2 : KsubU_cat K)

#check U1 ⊓ U2-/

/-- The morphism  U1 ⊓ U2 ⟶ U1 for elements of (KsubU_cat K P)-/
def InfInLeftKSU (U1 U2 : KsubU_cat K P): (InfKsubU K axiomP U1 U2) ⟶ U1:= homOfLE (by simp)

/-- The morphism U1 ⊓ U2 ⟶ U2 for elements of (KsubU_cat K P)-/
def InfInRightKSU (U1 U2 : KsubU_cat K P ): (InfKsubU K axiomP U1 U2) ⟶ U2 := homOfLE (by simp)

/-- The functor that send the pair (K1 ⊆ U1, K2 ⊆ U2) to K1 ⊓ K2 ⊆ U1 ∩ U2-/
@[simps]
def subK1SubK2toSubK1InterK2 (K1 K2 : Compacts X) [T2Space X]: (KsubU_cat K1) × (KsubU_cat K2 ) ⥤ KsubU_cat (K1 ⊓ K2) where
  obj U := ⟨ U.1.obj ⊓ U.2.obj, by
        constructor
        apply Set.inter_subset_inter
        exact U.1.property.1
        exact U.2.property.1
        rfl⟩
  map { U V } f := homOfLE ( by
    suffices U.1.obj ⊓ U.2.obj ≤ V.1.obj ∧ U.1.obj ⊓ U.2.obj ≤ V.2.obj by simpa
    exact ⟨Set.Subset.trans inf_le_left (leOfHom f.1), Set.Subset.trans inf_le_right (leOfHom f.2)⟩ )

include axiomP
/-- The evidence that the category (KsubU_cat K P) is cofiltered-/
lemma IsCofilteredKsubU : IsCofilteredOrEmpty (KsubU_cat K P) where
  cone_objs U1 U2 := by
    use InfKsubU K axiomP U1 U2
    use InfInLeftKSU K axiomP U1 U2
    use InfInRightKSU K axiomP U1 U2
  cone_maps U1 U2 _ _:= by
    use InfKsubU K axiomP U1 U2
    use InfInLeftKSU K axiomP U1 U2
    rfl

instance : Top (KsubU_cat K) := by
  use ⊤
  simp

instance : Bot (KsubU_cat (⊥ : Compacts X)) := by
  use ⊥
  simp

/-- The evidence that ⊥ is initial in the neighbourhouds of ⊥ -/
def IsInitialKsubUBot: IsInitial (⊥ :(KsubU_cat (⊥ : Compacts X))) := by
  apply IsInitial.ofUniqueHom
  · intro _ _
    apply eq_of_comp_right_eq
    intro _ _
    rfl
  · intro
    apply homOfLE
    intro _ hx
    rcases hx

/-- The evidence that op ⊥ is terminal in the neighbourhouds of op ⊥ -/
def IsTerminalKsubUOpBotOp: IsTerminal (op ⊥ : (KsubU_cat (⊥ : Compacts X))ᵒᵖ ) := by
  refine terminalOpOfInitial ?_
  exact IsInitialKsubUBot

instance : IsCofiltered (KsubU_cat K ) where
  toIsCofilteredOrEmpty := IsCofilteredKsubU K fun _ _ _ ↦ congrFun rfl

end

section
variable (K1 K2 : Compacts X)

/-- The functor that send the pair (K1 ⊆ U1, K2 ⊆ U2) to K1 ⊆ U1-/
@[simps!]
def KsubUK1K2ProjLeft : KsubU_cat K1 × KsubU_cat K2 ⥤ KsubU_cat K1 := (CategoryTheory.Prod.fst (KsubU_cat K1) (KsubU_cat K2))

instance : (KsubUK1K2ProjLeft K1 K2).Initial := by
  apply (Functor.initial_iff_of_isCofiltered _).mpr
  constructor
  · intro U
    use ⟨ U, ⊤⟩
    apply Nonempty.intro
    exact  𝟙 _
  · intro _ V _ _
    use V
    use 𝟙 _
    rfl

/-- The functor that send the pair (K1 ⊆ U1, K2 ⊆ U2) to K2 ⊆ U2-/
@[simps!]
def KsubUK1K2ProjRight : KsubU_cat K1 × KsubU_cat K2 ⥤ KsubU_cat K2 := (CategoryTheory.Prod.snd (KsubU_cat K1) (KsubU_cat K2))

instance : (KsubUK1K2ProjRight K1 K2).Initial := by
  apply (Functor.initial_iff_of_isCofiltered _).mpr
  constructor
  · intro U
    use ⟨ ⊤, U⟩
    apply Nonempty.intro
    exact  𝟙 _
  · intro _ V _ _
    use V
    use 𝟙 _
    rfl


instance [T2Space X]: (subK1SubK2toSubK1InterK2 K1 K2).Initial := by
  apply (Functor.initial_iff_of_isCofiltered _).mpr
  constructor
  · intro U
    -- c'est au moins vrai dans les metriques en épaissisant
    sorry
  · intro _ V _ _
    use V
    use 𝟙 _
    rfl

/-- The functor that send the pair (K1 ⊆ U1, K2 ⊆ U2) to K1 ⊆ U1 -/
@[simps]
def KsubUK1K2ProjCup: KsubU_cat K1 × KsubU_cat K2 ⥤ (KsubU_cat (K1 ⊔ K2) ) where
  obj U := ⟨ U.1.obj ⊔ U.2.obj, by
    constructor
    apply sup_le_sup
    · exact U.1.property.1
    · exact U.2.property.1
    rfl⟩
  map {U V } f := by
    apply homOfLE
    apply sup_le_sup
    exact leOfHom f.1
    exact leOfHom f.2

instance : (KsubUK1K2ProjCup K1 K2).Initial := by
  apply (Functor.initial_iff_of_isCofiltered _).mpr
  constructor
  · intro U
    use ⟨(K1subK2subU _ (homOfLE (le_sup_left))).obj U, (K1subK2subU _ (homOfLE (le_sup_right))).obj U⟩

    apply Nonempty.intro
    apply homOfLE
    simp

  · intro _ V _ _
    use V
    use 𝟙 _
    rfl

variable [T2Space X]

/-- The functor that send the pair (K1 ⊆ U1, K2 ⊆ U2) to the diagram U1 → U1 ∩ U2 ← U2-/
@[simps]
def UInterWC : (KsubU_cat K1 × KsubU_cat K2 )ᵒᵖ  ⥤ WalkingCospan ⥤ (Opens X)ᵒᵖ where
  obj U := cospan (op (homOfLE inf_le_left): op U.unop.1.obj ⟶ op (U.unop.1.obj ⊓ U.unop.2.obj) ) (op (homOfLE inf_le_right ): op U.unop.2.obj ⟶ op (U.unop.1.obj ⊓ U.unop.2.obj))
  map {U V} f := natTransCospan (op f.unop.1) (op ((subK1SubK2toSubK1InterK2 _ _).map f.unop)) (op f.unop.2) (rfl) (rfl)

/-- The functor Left projection: (K1 ⊆ U1, K2 ⊆ U2) ↦ U1 induced by UInterWC-/
@[simps!]
def jLeft : (KsubU_cat K1 × KsubU_cat K2 )ᵒᵖ ⥤ (Opens X)ᵒᵖ := (UInterWC K1 K2).flip.obj .left

/-- The functor Right projection: (K1 ⊆ U1, K2 ⊆ U2) ↦ U2 induced by UInterWC-/
@[simps!]
def jRight : (KsubU_cat K1 × KsubU_cat K2 )ᵒᵖ ⥤ (Opens X)ᵒᵖ := ( UInterWC K1 K2).flip.obj .right

/-- The functor "intersection" projection: (K1 ⊆ U1, K2 ⊆ U2) ↦ U1 ∩ U2 induced by UInterWC-/
@[simps!]
def jOne : (KsubU_cat K1 × KsubU_cat K2 )ᵒᵖ ⥤ (Opens X)ᵒᵖ := ( UInterWC K1 K2).flip.obj .one

/-- The functor "union" projection: (K1 ⊆ U1, K2 ⊆ U2) ↦ U1 ∩ U2-/
@[simps!]
def jCup : (KsubU_cat K1 × KsubU_cat K2 )ᵒᵖ ⥤ (Opens X)ᵒᵖ where
  obj U := op (U.unop.1.obj ⊔ U.unop.2.obj)
  map f := op (homOfLE (sup_le_sup (leOfHom f.unop.1) (leOfHom f.unop.2)
))

/-- The natural transformation from jLeft to jOne : (K1 ⊆ U1, K2 ⊆ U2) ↦ (U1 ∩ U2 ⟶ U1)   -/
def jLToJO : (jLeft K1 K2) ⟶ (jOne K1 K2) where
  app U := op (homOfLE (by simp))

/-- The natural transformation from jRight to jOne : (K1 ⊆ U1, K2 ⊆ U2) ↦ (U1 ∩ U2 ⟶ U2)-/
def jRToJO : (jRight K1 K2) ⟶ (jOne K1 K2) where
  app U := op (homOfLE (by simp))

/-- The natural transformation from jLeft to jOne : (K1 ⊆ U1, K2 ⊆ U2) ↦ (U1 ⟶ U1 ∪ U2)-/
def jCToJL : (jCup K1 K2) ⟶ (jLeft K1 K2)  where
  app U := op (homOfLE (by dsimp;simp))

/-- The natural transformation from jRight to jOne : (K1 ⊆ U1, K2 ⊆ U2) ↦ (U2 ⟶ U1 ∪ U2)-/
def jCToJR : (jCup K1 K2) ⟶ (jRight K1 K2) where
  app U := op (homOfLE (by simp))

/-- The equality isomorphism between the two ways defined in the file to see the operation (K1 ⊆ U1, K2 ⊆ U2) ↦ F(U1)-/
@[simps!]
def jCompFEqProjCompFULeft : (jLeft K1 K2 ⋙ F) ≅ (KsubUK1K2ProjLeft K1 K2).op ⋙ (FU K1 F) := eqToIso (by aesop)

/-- The equality isomorphism between the two ways defined in the file to see the operation (K1 ⊆ U1, K2 ⊆ U2) ↦ F(U2)-/
@[simps!]
def jCompFEqProjCompFURight : (jRight K1 K2 ⋙ F) ≅ (KsubUK1K2ProjRight K1 K2).op ⋙ (FU K2 F) := eqToIso (by aesop)

/-- The equality isomorphism between the two ways defined in the file to see the operation (K1 ⊆ U1, K2 ⊆ U2) ↦ F(U1 ∩ U2)-/
@[simps!]
def jCompFEqProjCompFUOne : (jOne K1 K2 ⋙ F) ≅ (subK1SubK2toSubK1InterK2 K1 K2).op ⋙ (FU (K1 ⊓ K2) F) := eqToIso (by aesop)

/-- The equality isomorphism between the two ways defined in the file to see the operation (K1 ⊆ U1, K2 ⊆ U2) ↦ F(U1 ∪ U2)-/
@[simps!]
def jCompFEqProjCompFUCup : (jCup K1 K2 ⋙ F) ≅ (KsubUK1K2ProjCup K1 K2).op ⋙ (FU (K1 ⊔ K2) F) := eqToIso (by aesop)

end

section
variable [T2Space X]
variable (K : Compacts X)

/-- The condition of being relatively compact-/
def relcCond : Opens X → Prop := fun (U : Opens X) => IsCompact (closure (U : Set X))

lemma axiomPrc : ∀ (U₁ U₂ : Opens X), relcCond U₁ → relcCond U₂ → relcCond (U₁ ⊓  U₂):= by
  intro U1 U2 h1 h2
  apply IsCompact.of_isClosed_subset
  · exact IsCompact.inter h1 h2
  · exact isClosed_closure
  · rw [ Opens.coe_inf]
    apply closure_inter_subset_inter_closure

/-- The category of opens neighbourhoods relatively compact of K-/
def RelCN_cat : Type u := (KsubU_cat K (relcCond))

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
  use ⟨interior L, isOpen_interior⟩
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
variable (K : Compacts X)

/-- The property of being a compact neighbourhood of K-/
def supSupK : Set (Compacts X) := fun (L : Compacts _) => (∃ (U: Opens _), (K.carrier ⊆ U.carrier) ∧ (U.carrier ⊆ L.carrier))

/-- The category of compacts neighbourhood of K-/
def supSupK_cat : Type u:= ObjectProperty.FullSubcategory (supSupK K )

instance : Category (supSupK_cat K ) := ObjectProperty.FullSubcategory.category (supSupK K)

lemma supSupKtoSupK (L : supSupK_cat K) : K.carrier ⊆ L.obj.carrier := by
  rcases L.property with ⟨U, hU1, hU2⟩
  exact hU1.trans hU2

lemma supSupKtoKsubInt (L : supSupK_cat K) : K.carrier ⊆ interior L.obj.carrier := by
  rcases L.property with ⟨U, hU1, hU2⟩
  intro _ hx
  use U
  constructor
  constructor
  · exact U.isOpen
  · exact hU2
  · exact hU1 hx

/-- a choice of an open between L and K-/
noncomputable def supSupKToKsubU ( L : supSupK_cat K) : KsubU_cat K where
  obj := Classical.choose L.property
  property := by
    constructor
    · exact (Classical.choose_spec L.property).1
    · rfl

variable [T2Space X]

/-- L1 ⊓ L2 as an element of (supSupK_cat K)-/
@[simps]
def InfSupSupK (L1 L2 : supSupK_cat K ) : (supSupK_cat K ) := ⟨(L1.obj) ⊓ (L2.obj), by
  rcases L1.property with ⟨U1,hU11,hU12⟩
  rcases L2.property with ⟨U2,hU21,hU22⟩

  use U1 ⊓ U2

  constructor
  · simp_all only [carrier_eq_coe, Opens.carrier_eq_coe, Opens.coe_inf, Set.subset_inter_iff, and_self]
  · suffices _ ∧ _ by simpa
    apply And.intro
    · apply subset_trans _ hU12
      exact Set.inter_subset_left
    · apply subset_trans _ hU22
      exact Set.inter_subset_right ⟩

/-- The morphisme L1 ⊓ L2 ⟶ L1 for elements of (supSupK_cat K)-/
def InfInLeftSSK (L1 L2 : supSupK_cat K ): (InfSupSupK K L1 L2) ⟶ L1 := homOfLE (by simp)

/-- The morphisme L1 ⊓ L2 ⟶ L2 for elements of (supSupK_cat K)-/
def InfInRightSSK (L1 L2 : supSupK_cat K ): (InfSupSupK K L1 L2) ⟶ L2 := homOfLE (by simp)

instance : IsCofilteredOrEmpty (supSupK_cat K) where
  cone_objs := by
    intro L1 L2
    use InfSupSupK K L1 L2
    use InfInLeftSSK K L1 L2
    use InfInRightSSK K L1 L2
  cone_maps := by
    intro L1 L2 i j
    use InfSupSupK K L1 L2
    use InfInLeftSSK K L1 L2
    rfl

variable [LocallyCompactSpace X]

instance : Nonempty (supSupK_cat K) := by
  have : IsOpen (⊤ : Set X)  := isOpen_univ
  have this2 : K.carrier ⊆ ⊤ := by
    intro _ _
    trivial
  rcases (exists_compact_between K.isCompact this this2 ) with ⟨L, hL⟩
  use ⟨L, hL.1⟩
  use ⟨interior L, isOpen_interior⟩
  constructor
  · exact hL.2.1
  · exact interior_subset

/-- The closure functor that send U ⊇ K relatively compact to overline(U) -/
@[simp]
def closureFuncK : RelCN_cat K ⥤ supSupK_cat K where
  obj U := ⟨⟨closure U.obj, U.property.2⟩, by
    use U.obj
    constructor
    exact U.property.1
    exact subset_closure ⟩
  map i :=  homOfLE <| closure_mono <| leOfHom i

omit [LocallyCompactSpace X] in
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

--#lint pourquoi n'est tu pas content?
