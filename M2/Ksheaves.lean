import Mathlib
import Mathlib.Topology.Separation
import Mathlib.CategoryTheory.Abelian.Basic

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite

variable (X) [TopologicalSpace X] [T2Space X]
variable (K : Compacts X)
variable {A} [Ring A]
variable (F : (Compacts X)ᵒᵖ ⥤ ModuleCat A) (K₁ :Compacts X) (K₂:Compacts X)

-- definiing the limit limit that apear in the axiom Ksh3

/-- The Propriety of being a relatively compact neighbouhood of K-/
def RelCN : Set (Opens X) := fun (U : Opens X) => (K.carrier ⊆ U.carrier) ∧ IsCompact (closure U : Set X)

/-- The category obtained by ordering by inclusion the opens satifying the previous property -/
def RelCN_cat : Type := FullSubcategory (RelCN X K)

instance : Category (RelCN_cat X K) := FullSubcategory.category (RelCN X K)

/-- Taking the closure of a relatively compact subset gives a map from RelCN_cat to Compacts that is increasing, and the defines a functor on the underling categories-/
@[simps]
def closureFunc : RelCN_cat X K ⥤ (Compacts X)  where
  obj U := ⟨closure U.obj, U.property.2⟩
  map f :=  homOfLE (closure_mono (leOfHom f))

/-- The Functor that represent the diagram composed of the F(overline{U}) together with the canonical maps-/
@[simps!]
def FUbar : (RelCN_cat X K)ᵒᵖ ⥤ (ModuleCat A) := (closureFunc X K).op.comp  F

/-- The natural transformation that allows to define F(K) as a cocone of the diagram FUbar-/
def FK_transNat: (FUbar X K F) ⟶ (Functor.const _ ).obj (op K) |>.comp F where
app W:= F.map <| op <| homOfLE <| by
  apply (W.unop).property.1.trans
  simp [subset_closure]
naturality _ _ _ := by
  suffices F.map _ ≫ F.map _ = F.map _ by simpa
  rw [← F.map_comp]
  rfl

/-- The cocone of the diagram FUbar given by F(K) and the canonical maps-/
@[simps]
def FK : Cocone (FUbar X K F):= Cocone.mk _ ((FK_transNat X K F)  ≫ ((Functor.constComp _ _ _).hom))

--the complex sheaf like in the axiom of K-sheaf

open ZeroObject
noncomputable section

variable {X}

/--The canonical map in (Compacts X)ᵒᵖ induced by K1 ⊆ K1 ⊔ K2-/
def toSupLeft : op (K₁ ⊔ K₂) ⟶ op K₁ := opHomOfLE le_sup_left
/--The canonical map in (Compacts X)ᵒᵖ induced by K2 ⊆ K1 ⊔ K2-/
def toSupRight : op (K₁ ⊔ K₂) ⟶ op K₂ := opHomOfLE le_sup_right

/--The canonical map in (Compacts X)ᵒᵖ induced by K1 ⊓ K2  ⊆ K1-/
def fromInfLeft : op K₁ ⟶ op (K₁ ⊓ K₂) := opHomOfLE inf_le_left
/--The canonical map in (Compacts X)ᵒᵖ induced by K1 ⊓ K2  ⊆ K2-/
def fromInfRight : op K₂ ⟶ op (K₁ ⊓ K₂) := opHomOfLE inf_le_right

@[simp]
lemma toSupLeft_comp_fromInf_left : toSupLeft K₁ K₂ ≫ fromInfLeft K₁ K₂ = opHomOfLE inf_le_sup := rfl

@[simp]
lemma toSupRight_comp_fromInf_rigt : toSupRight K₁ K₂ ≫ fromInfRight K₁ K₂ = opHomOfLE inf_le_sup := rfl

/--The zero map from 0 to F(K1 ∪ K2)-/
--@[simps!]
def ZtoFcup : 0 ⟶ F.obj <| op (K₁ ⊔ K₂) := 0

/-- The canonical map F(K1∪ K2)-> F(K1)⊞ F(K2) that sends a section to the sum of its restrictions-/
--@[simps!]
def FcuptoplusF: F.obj (op (K₁⊔ K₂)) ⟶ F.obj (op K₁) ⊞  F.obj (op K₂):= F.map (toSupLeft K₁ K₂) ≫ biprod.inl + F.map (toSupRight K₁ K₂) ≫ biprod.inr

/-- The canonical map F(K1)⊞ F(K2)-> F(K1∩ K2) that sends a sum of section to différence of their restrictions-/
--@[simps!]
def plusFtoFcap := biprod.fst ≫ F.map (fromInfLeft K₁ K₂) - biprod.snd ≫ F.map (fromInfRight K₁ K₂)

/--The short complex given by the three previous maps-/
@[simps!]
def complex : ComposableArrows (ModuleCat A) 3:= CategoryTheory.ComposableArrows.mk₃ (ZtoFcup F K₁ K₂)  (FcuptoplusF F K₁ K₂) (plusFtoFcap F K₁ K₂)

--#Lint does not like it
instance : (complex F K₁ K₂).IsComplex where
  zero := by
    intros i hi
    unfold complex ZtoFcup FcuptoplusF plusFtoFcap
    have hi' : i ≤ 1 := by simpa using hi
    set_option simprocs false in

    interval_cases i
    · -- F(K₁ ∪ K₂)-> F(K₁) ⊞ F(K₂)-> F(K₁) ⊞ F(K₂)-> F(K₁ ∩ K₂)=0
      simp
    · -- 0 -> F(K₁ ∪ K₂) -> F(K₁ ∪ K₂)-> F(K₁) ⊞ F(K₂)=0
      simp [← F.map_comp]

variable (X)

variable (A)
/-- The definition of J.pardon: A functor (Compacts X)ᵒᵖ ⥤ Ab that satify:
-a condition of zerology
-a finite exact sequence sheaf-like
-a condition of continuity-/

@[ext]
structure Ksheaf where
  /-- lint want's docs here-/
  carrier : (Compacts X)ᵒᵖ ⥤ ModuleCat A
  ksh1 : carrier.obj (op (⊥ : Compacts X)) = 0
  ksh2 : ∀ K₁ K₂ :Compacts X, (complex carrier K₁ K₂).Exact
  ksh3 : ∀ K : Compacts X, (IsIso (colimit.desc (FUbar X K carrier) (FK X K carrier)))


#check Ksheaf
instance :  Category (Ksheaf X A) := InducedCategory.category (·.carrier)

#check (inducedFunctor fun (F : Ksheaf X A) ↦ F.carrier : (Ksheaf X A )⥤ _ )

--deux trucs qui marchent pas mais sont bizzares
--#lint
