import M2.alpha
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Order.Lattice

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite

variable {X} [TopologicalSpace X] --[T2Space X]
variable (C) [Category C] [HasPullbacks C] [HasColimits C] [HasLimits C] [HasZeroObject C]


noncomputable section
variable (K : Compacts X) (U : Opens X)
variable (F : (Opens X)ᵒᵖ ⥤ C)

--a^* P et a^*Q are naturaly isomorphic if P et Q are nice enough
section

variable {P Q : Opens X → Prop} (hpq : ∀ (U : Opens X), P U → Q U) (axiomP : ∀ U1 U2, P U1 → P U2 → P (U1 ⊓ U2))
--variable {K1 K2 : Compacts X} (f : K1 ⟶ K2)

/-- U1⊓ U2 as an element of (KsubU_cat K P)ᵒᵖ-/
@[simps]
def InfKsubU (U1 U2 :(KsubU_cat K P)ᵒᵖ ): (KsubU_cat K P)ᵒᵖ:= ⟨( U1.unop.obj ⊓ U2.unop.obj), ⟨le_inf U1.unop.property.1 U2.unop.property.1, axiomP _ _ U1.unop.property.2 U2.unop.property.2⟩ ⟩

/-- The morphisme U1 ⟶ U1 ⊓ U2 for elements of (KsubU_cat K P)ᵒᵖ-/
def LeftInInf (U1 U2 :(KsubU_cat K P)ᵒᵖ ): U1 ⟶ (InfKsubU K axiomP U1 U2):= op (homOfLE (by simp))

/-- The morphisme U2 ⟶ U1 ⊓ U2 for elements of (KsubU_cat K P)ᵒᵖ-/
def RightInInf (U1 U2 :(KsubU_cat K P)ᵒᵖ ): U2 ⟶ (InfKsubU K axiomP U1 U2):= op (homOfLE (by simp))

/-- The functor induced by P -> Q from the category of opens that contains K and satiffy P to the one that satisfy Q-/
@[simps!]
def KsubUPtoQ : (KsubU_cat K P) ⥤  (KsubU_cat K Q ):= FullSubcategory.map (fun _ => fun hP => ⟨hP.1, hpq _ hP.2⟩)

@[simp]
lemma KsubPtoQCompFQEqFP : (KsubUPtoQ K hpq).op ⋙ FU K F Q = FU K F P := by rfl

variable (V : ∀ K, KsubU_cat K Q → KsubU_cat K P)

variable (V_spec : ∀ K,∀ U, (V K U).obj.carrier ⊆ U.obj.carrier)

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

  suffices _ = colimit.ι (FU _ _ _) ( op <| (K1subK2subU _ _ _ _ ).obj <| (KsubUPtoQ _ hpq).obj J.unop ) by simpa

  have : colimit.ι (FU _ _ _ ) ( op <| (K1subK2subU _ _ _ f.unop).obj J.unop ) ≫
    colimit.pre (FU _ _ _) (KsubUPtoQ _ hpq).op =
  colimit.ι (FU _ F _) (op <| (KsubUPtoQ _ hpq).obj <| (K1subK2subU _ _ _ f.unop).obj J.unop )  := by
    exact colimit.ι_pre (FU _ _ _) (Functor.op (KsubUPtoQ _ hpq)) ( op <| (K1subK2subU _ _ _ _).obj J.unop )

  rw [this]
  rfl

/-- The morphism from α_P to α_Q induced by the natural transformation AlphaUpFPtoQ -/
@[simps]
def AlphaUpPPtoQ : (AlphaUpStarP P)⟶ (@AlphaUpStarP _ _ C _ _ Q) where
  app _ := AlphaUpFPtoQ C _  hpq
  naturality F1 F2 _ := by
    ext _
    apply colimit.hom_ext
    intro U
    suffices _ = _ ≫ colimit.pre _ (KsubUPtoQ _ _).op ≫ colimMap (τres _ _ _ _ _) by simpa
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

include axiomP
--Implicit argument are an issue for infering the instance
/-- The evidence that the category (KsubU_cat K P)ᵒᵖ is filtered-/
lemma IsFilteredKsubU: IsFilteredOrEmpty (KsubU_cat K P)ᵒᵖ where
  cocone_objs U1 U2 := by
    use InfKsubU K axiomP U1 U2
    use LeftInInf K axiomP U1 U2
    use RightInInf K axiomP U1 U2
  cocone_maps U1 U2 _ _:= by
    use InfKsubU K axiomP U1 U2
    use RightInInf K axiomP U1 U2
    rfl

include V V_spec
--Implicit argument are an issue for infering the instance
/-- The evidence that the functor op (KsubUPtoQ K hpq) is final-/
lemma IsFinalOpKsubUPtoQ: Functor.Final (Functor.op (KsubUPtoQ K hpq)) := by
  have := @IsFilteredKsubU _ _ K _ axiomP
  apply ( Functor.final_iff_of_isFiltered _ ).2
  constructor
  · intro U
    use op ( V K U.unop)
    apply Nonempty.intro
    apply op
    apply homOfLE
    apply V_spec
  · intro _ U2 _ _
    use U2
    use 𝟙 _
    rfl

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

section --α^* variante avec seulement les U relativements comapcts

variable (X)
variable [LocallyCompactSpace X] [T2Space X]

--P
/-- the condition of being relatively compact-/
def relcCond : Opens X → Prop := fun (U:Opens X) => IsCompact (closure (U:Set X))
--Q
#check trueCond

/-- The functor α^* with condition on the opens of being relatively compact-/
def AlphaUpStarRc : ((Opens X)ᵒᵖ ⥤ C) ⥤ (Compacts X)ᵒᵖ ⥤ C := AlphaUpStarP (relcCond X)

--hpq is trivial and #lint complain if an explicit proof is given

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

lemma axiomP : ∀ U₁ U₂, relcCond X U₁ → relcCond X U₂ → relcCond X (U₁ ⊓  U₂):= by
  intro U1 U2 h1 h2
  unfold relcCond
  apply IsCompact.of_isClosed_subset
  · apply IsCompact.inter
    · exact h1
    · exact h2
  · exact isClosed_closure
  · rw [ Opens.coe_inf]
    apply closure_inter_subset_inter_closure

/-- The evidence that AlphaUpStarRc X C  and AlphaUpStar are isomorphics -/
def AlphaUpStarToRc :  AlphaUpStarRc X C ≅ AlphaUpStar :=  IsoAlphaUpPtoQ _ (λ _ _ => rfl) (axiomP X) (V X) (V_spec
X)
/-- The data of the adjunction betwee α^*RC and α_* deduced by the previous isomorphism and the adjunction of α^* and α_*-/
def AdjAlphaStarRc : AlphaUpStarRc X C ⊣ AlphaDownStar := AdjAlphaStar.ofNatIsoLeft (AlphaUpStarToRc X C).symm

#lint
