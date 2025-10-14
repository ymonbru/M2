import M2.KsubU

open CategoryTheory Limits TopologicalSpace Compacts Opposite

universe u v w

variable {X :Type w} [TopologicalSpace.{w} X] [T2Space.{w} X]
variable (K : Compacts X)

variable {C : Type u} [Category.{v, u} C]
variable (F : (Compacts X)ᵒᵖ ⥤ C) (K₁ :Compacts X) (K₂:Compacts X)

-- definiing the limit that apear in the axiom Ksh3

/-- Taking the closure of a relatively compact subset gives a map from RelCN_cat to Compacts that is increasing, and the defines a functor on the underling categories-/
@[simps!]
def closureFunc : RelCN_cat K ⥤ (Compacts X)  := (closureFuncK K).comp (ObjectProperty.ι (supSupK K))

/-- The Functor that represent the diagram composed of the F(overline{U}) together with the canonical maps-/
@[simps!]
def FUbar : (RelCN_cat K)ᵒᵖ ⥤ C := (closureFunc K).op.comp  F

/-- The natural transformation that allows to define F(K) as a cocone of the diagram FUbar-/
@[simps]
def FUbarToFK_transNat: (FUbar K F) ⟶ (Functor.const _ ).obj (op K) |>.comp F where
app W:= F.map <| op <| homOfLE <| by
  apply (W.unop).property.1.trans
  simp [subset_closure]
naturality _ _ _ := by
  suffices _ = F.map _ by simpa
  rw [← F.map_comp]
  rfl

/-- The cocone of the diagram FUbar given by F(K) and the canonical maps-/
@[simps]
def FUbarToFK : Cocone (FUbar K F) := Cocone.mk _ <| (FUbarToFK_transNat K F)  ≫ (Functor.constComp _ _ _).hom

/-- The Functor that represent the diagram obtained by restricting F to the compacts that contain strictly K-/
@[simps!]
def FresSSK : (supSupK_cat K)ᵒᵖ ⥤ C := (ObjectProperty.ι (supSupK K)).op.comp F

/-- The natural transformation that allows to define F(K) as a cocone of the diagram FresSSK-/
@[simps]
def FLToFKι: (FresSSK K F) ⟶ (Functor.const _ ).obj (op K) |>.comp F where
app W:= F.map <| op <| homOfLE <| by
  apply supSupKtoSupK
naturality _ _ _ := by
  suffices _ = F.map _ by simpa
  rw [← F.map_comp]
  rfl

/-- The cocone of the diagram FresSSK given by F(K) and the canonical maps-/
@[simps]
def FLToFK : Cocone (FresSSK K F) := Cocone.mk _ <| (FLToFKι K F)  ≫ (Functor.constComp _ _ _).hom

variable [LocallyCompactSpace X]

/-- The evidence that the colimit can be computed in two diferent ways-/
@[simps!]
noncomputable def FUbarEquivFL : IsColimit (FUbarToFK K F) ≃ IsColimit (FLToFK K F) := Functor.Final.isColimitWhiskerEquiv (closureFuncK K).op  (FLToFK K F)


--the pullback square that gives a complex sheaf like in some good cases in the axiom of K-sheaf

--open ZeroObject
noncomputable section

/-
/--The canonical map in (Compacts X)ᵒᵖ induced by K1 ⊆ K1 ⊔ K2-/
def toSupLeft : op (K₁ ⊔ K₂) ⟶ op K₁ := opHomOfLE le_sup_left
/--The canonical map in (Compacts X)ᵒᵖ induced by K2 ⊆ K1 ⊔ K2-/
def toSupRight : op (K₁ ⊔ K₂) ⟶ op K₂ := opHomOfLE le_sup_right

/-The canonical map in (Compacts X)ᵒᵖ induced by K1 ⊓ K2  ⊆ K1-/
def fromInfLeft : op K₁ ⟶ op (K₁ ⊓ K₂) := opHomOfLE inf_le_left
/--The canonical map in (Compacts X)ᵒᵖ induced by K1 ⊓ K2  ⊆ K2-/
def fromInfRight : op K₂ ⟶ op (K₁ ⊓ K₂) := opHomOfLE inf_le_right


lemma toSupLeft_comp_fromInf_left : toSupLeft K₁ K₂ ≫ fromInfLeft K₁ K₂ = opHomOfLE inf_le_sup := rfl

lemma toSupRight_comp_fromInf_rigt : toSupRight K₁ K₂ ≫ fromInfRight K₁ K₂ = opHomOfLE inf_le_sup := rfl -/

/-- The canonical map F(K₁) ⟶ F(K₁ ⊓ K₂)-/
def FtoFInfLeft : F.obj (op K₁) ⟶ F.obj (op (K₁ ⊓ K₂)) := F.map (opHomOfLE inf_le_left)

/-- The canonical map F(K₂) ⟶ F(K₁ ⊓ K₂)-/
def FtoFInfRight : F.obj (op K₂) ⟶ F.obj (op (K₁ ⊓ K₂)):= F.map (opHomOfLE inf_le_right)

/-- The canonical map F(K₁ ⊔  K₂) ⟶ F( K₁)-/
def FSuptoFLeft : F.obj (op (K₁ ⊔  K₂)) ⟶ F.obj (op K₁) := F.map (opHomOfLE le_sup_left)

/-- The canonical map F(K₁ ⊔  K₂) ⟶ F( K₂)-/
def FSuptoFRight : F.obj (op (K₁ ⊔  K₂)) ⟶ F.obj (op K₂) := F.map (opHomOfLE le_sup_right)

/-- The commutative square F(K₁ ⊔  K₂) ⟶ F(K₁) ⟶ F(K₁ ⊓ K₂) = F(K₁ ⊔  K₂) ⟶ F(K₂) ⟶ F(K₁ ⊓ K₂) as a pullback cone -/
@[simps!]
def SquareSuptoInf : PullbackCone (FtoFInfLeft F K₁ K₂) ( FtoFInfRight _ _ _):= by
  apply PullbackCone.mk (FSuptoFLeft _ _ _) (FSuptoFRight _ _ _)
  repeat erw [← F.map_comp]
  rfl

/-
/--The zero map from 0 to F(K1 ∪ K2)-/
--@[simps]
def ZtoFcup : 0 ⟶ F.obj <| op (K₁ ⊔ K₂) := 0

/-- The canonical map F(K1∪ K2)-> F(K1)⊞ F(K2) that sends a section to the sum of its restrictions-/
--@[simps!]
def FcuptoplusF: F.obj (op (K₁⊔ K₂)) ⟶ F.obj (op K₁) ⊞  F.obj (op K₂):= F.map (toSupLeft K₁ K₂) ≫ biprod.inl + F.map (toSupRight K₁ K₂) ≫ biprod.inr

/-- The canonical map F(K1)⊞ F(K2)-> F(K1∩ K2) that sends a sum of section to différence of their restrictions-/
--@[simps!]
def plusFtoFcap := biprod.fst ≫ F.map (fromInfLeft K₁ K₂) - biprod.snd ≫ F.map (fromInfRight K₁ K₂)

/--The short complex given by the three previous maps-/
--@[simps!]
def complex : ComposableArrows (ModuleCat A) 3:= CategoryTheory.ComposableArrows.mk₃ (ZtoFcup F K₁ K₂)  (FcuptoplusF F K₁ K₂) (plusFtoFcap F K₁ K₂)
open ProofWidgets

lemma FisCplx : (complex F K₁ K₂).IsComplex where
  zero := by
    intros i hi
    unfold complex ZtoFcup FcuptoplusF plusFtoFcap
    have hi' : i ≤ 1 := by simpa using hi
    set_option simprocs false in
    interval_cases i
    · -- F(K₁ ∪ K₂)-> F(K₁) ⊞ F(K₂)-> F(K₁) ⊞ F(K₂)-> F(K₁ ∩ K₂)=0
      --with_panel_widgets [GoalTypePanel]
      simp
    · -- 0 -> F(K₁ ∪ K₂) -> F(K₁ ∪ K₂)-> F(K₁) ⊞ F(K₂)=0
      simp [← F.map_comp]-/

variable (X) (C)

/-- An extension of the definition of J.pardon: A functor (Compacts X)ᵒᵖ ⥤ C -/

@[ext]
structure Ksheaf where
  /-- The K-preshaef that has the property of being a sheaf-/
  carrier : (Compacts X)ᵒᵖ ⥤ C
  /--The empty set is sent to 0_C-/
  ksh1 : IsTerminal (carrier.obj (op (⊥ : Compacts _)))
  /--There is a pullback square -/
  ksh2 : ∀ K₁ K₂ :Compacts X, IsLimit (SquareSuptoInf carrier K₁ K₂ )
  /--A continuity condition that state that a "regular function on K" is defined at the neighbourhood of K-/
  ksh3 : ∀ K : Compacts X, (IsColimit (FLToFK K carrier))

instance :  Category (Ksheaf X C) := InducedCategory.category (·.carrier)

/-- the forget functor from Ksheaf to K-presheaf-/
@[simps!]
def KsheafToPre : (Ksheaf X C ) ⥤ (Compacts X)ᵒᵖ ⥤ C := inducedFunctor fun (F : Ksheaf X C) ↦ F.carrier

/--The evidence that KsheafToPre is fullyfaithful-/
instance KsheafToPreIsFF: (KsheafToPre X C).FullyFaithful  := fullyFaithfulInducedFunctor fun (F : Ksheaf X C) ↦ F.carrier

-- pourquoi diable il ne le devine pas seul?
instance : (KsheafToPre X C).Faithful := by
  apply Functor.FullyFaithful.faithful
  exact KsheafToPreIsFF X C

instance : (KsheafToPre X C).Full := by
  apply Functor.FullyFaithful.full
  exact KsheafToPreIsFF X C

--#lint
