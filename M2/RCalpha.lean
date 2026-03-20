import M2.alpha

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
def KsubUPtoQ : (KsubU_cat K P) ⥤ (KsubU_cat K Q ):= ObjectProperty.ιOfLE (fun _ => fun hP => ⟨hP.1, hpq _ hP.2⟩)

--omit [HasPullbacks C] [HasColimits C] [HasLimits C]
--@[simp]
--lemma KsubPtoQCompFQEqFP : (KsubUPtoQ K hpq).op ⋙ FU K F Q = FU K F P := by rfl

variable (V : ∀ K, KsubU_cat K Q → KsubU_cat K P)

variable (V_spec : ∀ K,∀ U, (V K U).obj.carrier ⊆ U.obj.carrier)

variable [HasColimitsOfSize.{w, w} C] [HasLimitsOfSize.{w, w} C]

set_option backward.isDefEq.respectTransparency false in
/-- The morphisme from α_P F to α_Q F induced by the inclusion of (KsubU_cat K P) into (KsubU_cat K Q )-/
@[simps]
def AlphaUpFPtoQ : (AlphaUpStarF F P) ⟶ (AlphaUpStarF F Q) where
app K := colimit.pre (FU K.unop _ _) (Functor.op (KsubUPtoQ K.unop hpq))
naturality K L f:= by
  apply colimit.hom_ext
  intro J
  -- ça on devrais pourvoir le plier avec une tactique du genre forceColimW : TODO

  rw [ ← Category.assoc, ← Category.assoc]
  --rw [colimit.ι_pre (FU _ F Q) (Functor.op (KsubUPtoQ _ hpq)) J]

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

set_option backward.isDefEq.respectTransparency false in
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
      constructor
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

variable {X}  {C}
/-- The functor α^* with condition on the opens of being relatively compact-/
@[simps!]
def AlphaUpStarRc : ((Opens X)ᵒᵖ ⥤ C) ⥤ (Compacts X)ᵒᵖ ⥤ C := AlphaUpStarP (relcCond)

variable (X) (C)
--hpq is trivial and #lint complain if an explicit proof is given

omit [T2Space X] in
lemma existsIntermedKAndU (h : K.carrier ⊆ U.carrier) : Nonempty ({ L //IsCompact L ∧ K.carrier ⊆ interior L ∧ L ⊆ U.carrier}) := by
  let ⟨L,hL⟩ := (exists_compact_between K.isCompact U.isOpen h )
  exact Nonempty.intro ⟨L,hL⟩

/-- The V such that K sub V sub Vbar sub U for X localy comapcts-/
def Vloc : KsubU_cat K → (RelCN_cat K )  := by
  intro U
  let L := (Classical.choice (existsIntermedKAndU X K U.obj U.property.1)).val
  use ⟨interior L, isOpen_interior ⟩
  constructor
  · exact (Classical.choice (existsIntermedKAndU X K U.obj U.property.1)).property.2.1
  · apply IsCompact.of_isClosed_subset
    · exact (Classical.choice (existsIntermedKAndU X K U.obj U.property.1)).property.1
    · apply isClosed_closure
    · intro _ ha
      apply ha
      constructor
      · apply IsCompact.isClosed
        exact (Classical.choice (existsIntermedKAndU X _ U.obj U.property.1)).property.1
      · apply interior_subset

-- probabelement refaire ces deux lemmes dans un meilleur format et un meilleur nom
lemma V_spec : ∀ U, (Vloc X K U).obj.carrier ⊆ U.obj:= by
  intro U
  apply Set.Subset.trans
  apply interior_subset
  exact (Classical.choice (existsIntermedKAndU X _ _ U.property.1)).property.2.2

lemma V_closure : ∀ U, ((closureFunc K).obj (Vloc X K U)).carrier ⊆ U.obj := by
  intro U
  apply Set.Subset.trans _
  exact (Classical.choice (existsIntermedKAndU X _ _ U.property.1)).property.2.2
  apply Set.Subset.trans _
  apply closure_subset_iff_isClosed.2
  apply IsCompact.isClosed
  exact (Classical.choice (existsIntermedKAndU X _ _ U.property.1)).property.1

  apply closure_mono
  apply interior_subset

lemma V_interior : ∀ U, K.carrier ⊆ interior (Vloc X K U).obj.carrier  := by
  intro U
  simp [Vloc]
  exact (Classical.choice (existsIntermedKAndU X _ _ U.property.1)).property.2.1

/-- The evidence that AlphaUpStarRc X C  and AlphaUpStar are isomorphics -/
@[simps!]
def AlphaUpStarToRc :  (@AlphaUpStarRc C _ X _ _) ≅ AlphaUpStar :=  IsoAlphaUpPtoQ _ (λ _ _ => rfl) (axiomPrc ) (Vloc X) (V_spec
X)
/-- The data of the adjunction betwee α^*RC and α_* deduced by the previous isomorphism and the adjunction of α^* and α_*-/
@[simps!]
def AdjAlphaStarRc : (@AlphaUpStarRc C _ X _ _) ⊣ AlphaDownStar := AdjAlphaStar.ofNatIsoLeft (AlphaUpStarToRc C X).symm

#lint
