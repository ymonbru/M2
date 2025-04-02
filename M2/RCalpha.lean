import M2.alpha
import M2.KsubU
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Order.Lattice

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite

universe u v w

variable {X : Type w} [TopologicalSpace X]
variable (C : Type u) [Category.{v, u} C]


noncomputable section
variable (K : Compacts X) (U : Opens X)
variable (F : (Opens X)ᵒᵖ ⥤ C)

--a^* P et a^*Q are naturaly isomorphic if P et Q are nice enough

variable {P Q : Opens X → Prop} (hpq : ∀ (U : Opens X), P U → Q U) (axiomP : ∀ U1 U2, P U1 → P U2 → P (U1 ⊓ U2))
--variable {K1 K2 : Compacts X} (f : K1 ⟶ K2)

/-- The functor induced by P -> Q from the category of opens that contains K and satiffy P to the one that satisfy Q-/
@[simps!]
def KsubUPtoQ : (KsubU_cat K P) ⥤  (KsubU_cat K Q ):= FullSubcategory.map (fun _ => fun hP => ⟨hP.1, hpq _ hP.2⟩)

--omit [HasPullbacks C] [HasColimits C] [HasLimits C]
@[simp]
lemma KsubPtoQCompFQEqFP : (KsubUPtoQ K hpq).op ⋙ FU K F Q = FU K F P := by rfl

variable (V : ∀ K, KsubU_cat K Q → KsubU_cat K P)

variable (V_spec : ∀ K,∀ U, (V K U).obj.carrier ⊆ U.obj.carrier)

variable [HasColimitsOfSize.{w, w} C] [HasLimitsOfSize.{w, w} C]
/-- The morphisme from α_P F to α_Q F induced by the inclusion of (KsubU_cat K P) into (KsubU_cat K Q )-/
@[simps]
def AlphaUpFPtoQ : (AlphaUpStarF F P) ⟶ (AlphaUpStarF F Q) where
app K := colimit.pre (FU K.unop _ _) (Functor.op (KsubUPtoQ K.unop hpq))
naturality K L f:= by

  apply colimit.hom_ext
  intro J
  rw [ ← Category.assoc, ← Category.assoc]
  have : colimit.ι (FU _ _ _) J ≫ colimit.pre (FU _ _ _) (KsubUPtoQ _ hpq).op =
  colimit.ι (FU _ F _) (op <| (KsubUPtoQ _ hpq).obj J.unop ) := by
    exact colimit.ι_pre (FU _ _ _) (Functor.op (KsubUPtoQ _ hpq)) J

  rw [this]

  suffices _ = colimit.ι (FU _ _ _) ( op <| (K1subK2subU _ _ ).obj <| (KsubUPtoQ _ hpq).obj J.unop ) by simpa

  have : colimit.ι (FU _ _ _ ) ( op <| (K1subK2subU _ f.unop).obj J.unop ) ≫
    colimit.pre (FU _ _ _) (KsubUPtoQ _ hpq).op =
  colimit.ι (FU _ F _) (op <| (KsubUPtoQ _ hpq).obj <| (K1subK2subU _ f.unop).obj J.unop )  := by
    exact colimit.ι_pre (FU _ _ _) (Functor.op (KsubUPtoQ _ hpq)) ( op <| (K1subK2subU _ _).obj J.unop )

  rw [this]
  rfl

/-- The morphism from α_P to α_Q induced by the natural transformation AlphaUpFPtoQ -/
@[simps]
def AlphaUpPPtoQ : (AlphaUpStarP P) ⟶ (@AlphaUpStarP _ _ C _ _ Q) where
  app _ := AlphaUpFPtoQ C _  hpq
  naturality F1 F2 _ := by
    ext _
    apply colimit.hom_ext
    intro U
    suffices _ = _ ≫ colimit.pre _ (KsubUPtoQ _ _).op ≫ colimMap (τres _ _ _) by simpa
    rw [ ← Category.assoc,← Category.assoc]
    have : colimit.ι (FU _ _ _) U ≫ colimit.pre (FU _ _ _ ) (KsubUPtoQ _ hpq).op =
  colimit.ι (FU _ F1 _) (op <| (KsubUPtoQ _ hpq).obj _ ) := by
      exact colimit.ι_pre (FU _ _ _) (KsubUPtoQ _ hpq).op _
    rw [this]
    suffices _ = _ ≫ colimit.ι (FU _ _ _) (op <| (KsubUPtoQ _ hpq).obj U.unop )  by simpa
    apply whisker_eq
    have : colimit.ι (FU _ _ _ ) U ≫ colimit.pre (FU _ _ _ ) (KsubUPtoQ _ hpq).op =
  colimit.ι (FU _ F2 _ ) ( op <| (KsubUPtoQ _ hpq).obj U.unop ) := by
      exact colimit.ι_pre (FU _ _ _) (KsubUPtoQ _ hpq).op _

    rw [this]

include axiomP V V_spec
--Implicit argument are an issue for infering the instance
/-- The evidence that the functor op (KsubUPtoQ K hpq) is final-/
lemma IsFinalOpKsubUPtoQ: Functor.Final (Functor.op (KsubUPtoQ K hpq)) := by
  have := @IsCofilteredKsubU _ _ K _ axiomP

  have : (KsubUPtoQ K hpq).Initial := by
    apply (Functor.initial_iff_of_isCofiltered _).2
    constructor
    · intro U
      use ( V K U)
      apply Nonempty.intro
      apply homOfLE
      apply V_spec
    · intro _ U _ _
      use U
      use 𝟙 _
      rfl
  apply Functor.final_op_of_initial

omit [HasLimitsOfSize.{w, w} C] in
lemma IsIsoAlphaUpPtoQ : IsIso (AlphaUpPPtoQ C hpq):= by
  apply ( NatTrans.isIso_iff_isIso_app _).2
  intro _
  apply ( NatTrans.isIso_iff_isIso_app _).2
  intro K
  have := @IsFinalOpKsubUPtoQ _ _ K.unop _ _ hpq axiomP _ V_spec--j'aimerais vraiment qu'il le devine
  exact Functor.Final.colimit_pre_isIso (KsubUPtoQ _ hpq).op

/-- The evidence that α_P and α_Q are isomorphics-/
def IsoAlphaUpPtoQ : (AlphaUpStarP P) ≅ (@AlphaUpStarP _ _ C _ _ Q):= by
  have:= IsIsoAlphaUpPtoQ C hpq axiomP _ V_spec
  apply asIso (AlphaUpPPtoQ C hpq)

end
 --α^* variante avec seulement les U relativements comapcts
noncomputable section

variable (X : Type w) [TopologicalSpace X] [LocallyCompactSpace.{w} X] [T2Space X] (K : Compacts X) (U : Opens X)

variable [HasColimitsOfSize.{w, w} C] [HasLimitsOfSize.{w, w} C]

/-- The functor α^* with condition on the opens of being relatively compact-/
def AlphaUpStarRc : ((Opens X)ᵒᵖ ⥤ C) ⥤ (Compacts X)ᵒᵖ ⥤ C := AlphaUpStarP (relcCond)

--hpq is trivial and #lint complain if an explicit proof is given

omit [T2Space X] in
lemma existsIntermed (h : K.carrier ⊆ U.carrier) : Nonempty ({ L //IsCompact L ∧ K.carrier ⊆ interior L ∧ L ⊆ U.carrier}) := by
  rcases (exists_compact_between K.isCompact U.isOpen h ) with ⟨L,hL⟩
  exact Nonempty.intro ⟨L,hL⟩

/-- The V such that K sub V sub Vbar sub U for X localy comapcts-/
def V K : KsubU_cat K (trueCond) → KsubU_cat K (@relcCond X _ ) := by
  intro U
  let L:=(Classical.choice (existsIntermed X K U.obj U.property.1)).val
  use ⟨interior L,@isOpen_interior X L _⟩
  constructor
  · exact (Classical.choice (existsIntermed X K U.obj U.property.1)).property.2.1
  · apply IsCompact.of_isClosed_subset
    · exact (Classical.choice (existsIntermed X K U.obj U.property.1)).property.1
    · apply isClosed_closure
    · intro _ ha
      apply ha
      constructor
      · apply IsCompact.isClosed
        exact (Classical.choice (existsIntermed X _ U.obj U.property.1)).property.1
      · apply interior_subset

lemma V_spec : ∀ K,∀ U, (V X K U).obj.carrier ⊆ U.obj:= by
  intro _ U
  unfold V
  apply Set.Subset.trans
  apply interior_subset
  exact (Classical.choice (existsIntermed X _ _ U.property.1)).property.2.2

/-- The evidence that AlphaUpStarRc X C  and AlphaUpStar are isomorphics -/
def AlphaUpStarToRc :  AlphaUpStarRc C X ≅ AlphaUpStar :=  IsoAlphaUpPtoQ _ (λ _ _ => rfl) (axiomPrc ) (V X) (V_spec
X)
/-- The data of the adjunction betwee α^*RC and α_* deduced by the previous isomorphism and the adjunction of α^* and α_*-/
def AdjAlphaStarRc : AlphaUpStarRc C X ⊣ AlphaDownStar := AdjAlphaStar.ofNatIsoLeft (AlphaUpStarToRc C X).symm

#lint
