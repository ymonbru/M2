import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Topology.Sets.Compacts
import Mathlib.CategoryTheory.Filtered.Basic
import M2.KsubU


open CategoryTheory Limits TopologicalSpace Compacts Opposite

variable (X) [TopologicalSpace X] [T2Space X]
variable (K : Compacts X)
variable {C} [Category C] [HasPullbacks C] [HasColimits C] [HasZeroObject C]
--variable {A} [Ring A]
variable (F : (Compacts X)ᵒᵖ ⥤ C) (K₁ :Compacts X) (K₂:Compacts X)

-- definiing the limit limit that apear in the axiom Ksh3

/-- Taking the closure of a relatively compact subset gives a map from RelCN_cat to Compacts that is increasing, and the defines a functor on the underling categories-/
@[simps]
def closureFunc : RelCN_cat X K ⥤ (Compacts X)  where
  obj U := ⟨closure U.obj, U.property.2⟩
  map _ :=  homOfLE <| closure_mono <| leOfHom _

/-- The Functor that represent the diagram composed of the F(overline{U}) together with the canonical maps-/
@[simps!]
def FUbar : (RelCN_cat X K)ᵒᵖ ⥤ C := (closureFunc X K).op.comp  F

/-- The natural transformation that allows to define F(K) as a cocone of the diagram FUbar-/
def FK_transNat: (FUbar X K F) ⟶ (Functor.const _ ).obj (op K) |>.comp F where
app W:= F.map <| op <| homOfLE <| by
  apply (W.unop).property.1.trans
  simp [subset_closure]
naturality _ _ _ := by
  suffices _ = F.map _ by simpa
  rw [← F.map_comp]
  rfl

/-- The cocone of the diagram FUbar given by F(K) and the canonical maps-/
@[simps]
def FK : Cocone (FUbar X K F) := Cocone.mk _ <| (FK_transNat X K F)  ≫ (Functor.constComp _ _ _).hom

--the pullback square that gives a complex sheaf like in some good cases in the axiom of K-sheaf

open ZeroObject
noncomputable section

variable {X}

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
  ksh1 : carrier.obj (op (⊥ : Compacts _)) = 0
  /--There is a pullback square -/
  ksh2 : ∀ K₁ K₂ :Compacts X, IsLimit (SquareSuptoInf carrier K₁ K₂ )
  /--A continuity condition that state that a "regular function on K" is defined at the neighbourhood of K-/
  ksh3 : ∀ K : Compacts X, (IsColimit (FK _ K carrier))


#check Ksheaf

instance :  Category (Ksheaf X C) := InducedCategory.category (·.carrier)

#check (inducedFunctor fun (F : Ksheaf X C) ↦ F.carrier : (Ksheaf X C )⥤ _ )


#lint
