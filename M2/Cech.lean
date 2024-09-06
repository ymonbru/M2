
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.AlgebraicTopology.CechNerve
import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.AlgebraicTopology.ExtraDegeneracy

open CategoryTheory SimplicialObject.Augmented Opposite

noncomputable section

universe u v w

variable {C : Type u} [Category.{v} C]  [Small.{v, u} C]


variable (X:C)

variable (A: Type  v) [Ring A]

variable (F:C ᵒᵖ ⥤ ModuleCat A)

variable (U:Presieve X)

local notation "R" => Sieve.generate U

def Y : Cᵒᵖ⥤Type v := ∐ (fun (Z : C) => ∐ (fun (_ : @U Z) => yoneda.obj Z))

def tau_Z_f (Z:C) (f: @U Z): yoneda.obj Z ⟶ (Sieve.functor R) where
  app W a := ⟨(a ≫ f), Z, a, f, (f.2), by simp⟩

def τ:  (Y X U) ⟶ (Sieve.functor R) := (Limits.Sigma.desc (fun (Z:C) => Limits.Sigma.desc fun (f : @U Z) => (tau_Z_f X U Z f)))

/-lemma tau_epi: Epi (τ X U):= by
  constructor
  intros Z u v huv
  apply NatTrans.ext
  ext Z f
  rcases f with ⟨f,Y, g, h, hf1, hf2⟩
  --apply Subtype.ext


  sorry-/

variable (V:C)

#check (τ X U).app (op V)

def truc_local : SplitEpi (Arrow.mk ((τ X U).app (op V))).hom := by
  sorry
  --normalement c'est l'axiome du choix

def CechObjAugmented_local : SimplicialObject.Augmented (Type v) := (Arrow.mk ((τ X U).app (op V))).augmentedCechNerve

def ExtraDegeneracyCechObj_local : ExtraDegeneracy (CechObjAugmented_local X U V) := Arrow.AugmentedCechNerve.extraDegeneracy (Arrow.mk ((τ X U).app (op V))) (truc_local _ _ _)

def CechAugmented_local : SimplicialObject.Augmented ( ModuleCat  A) := ((whiskering (Type v) (ModuleCat A)).obj (ModuleCat.free A)).obj (CechObjAugmented_local X U V)

def ExtraDegeneracyCech_local : ExtraDegeneracy (CechAugmented_local X A U V) := ExtraDegeneracy.map  (ExtraDegeneracyCechObj_local X U V) (ModuleCat.free A)

#check ExtraDegeneracy.homotopyEquiv (ExtraDegeneracyCech_local X A U V)

def homotpyEquivLocal: HomotopyEquiv (AlgebraicTopology.AlternatingFaceMapComplex.obj (drop.obj (CechAugmented_local X A U V)))
((ChainComplex.single₀ (ModuleCat A)).obj (point.obj (CechAugmented_local X A U V))) := ExtraDegeneracy.homotopyEquiv (ExtraDegeneracyCech_local X A U V)


def truc : SplitEpi (Arrow.mk (τ X U)).hom := by
  sorry--Il faut le prendre localement, sinon c'est faux, la suite c'est juste pour avoir un exemple qui marche

def PresheafOfTypeToAMod : (Cᵒᵖ ⥤ Type v) ⥤ Cᵒᵖ ⥤ ModuleCat A := (whiskeringRight Cᵒᵖ  _ _).obj (ModuleCat.free A)

--def CechObj : SimplicialObject (Cᵒᵖ ⥤Type v) := (Arrow.mk (τ X U)).cechNerve

def CechObjAugmented : SimplicialObject.Augmented (Cᵒᵖ ⥤Type v) := (Arrow.mk (τ X U)).augmentedCechNerve

def ExtraDegeneracyCechObj : ExtraDegeneracy (CechObjAugmented X U) := Arrow.AugmentedCechNerve.extraDegeneracy (Arrow.mk (τ X U)) (truc _ _)

--def Cech : SimplicialObject (Cᵒᵖ ⥤ ModuleCat  A) :=  ((whiskeringRight SimplexCategoryᵒᵖ  (Cᵒᵖ⥤ Type v) (Cᵒᵖ⥤ ModuleCat A)).obj (PresheafOfTypeToAMod A)).obj (CechObj X U)

def CechAugmented : SimplicialObject.Augmented (Cᵒᵖ ⥤ ModuleCat  A) :=((whiskering (Cᵒᵖ ⥤ Type v) (Cᵒᵖ ⥤ ModuleCat A)).obj (PresheafOfTypeToAMod A)).obj (CechObjAugmented X U)

def ExtraDegeneracyCech : ExtraDegeneracy (CechAugmented X A U) := ExtraDegeneracy.map  (ExtraDegeneracyCechObj X U) (PresheafOfTypeToAMod A)

#check ExtraDegeneracy.homotopyEquiv (ExtraDegeneracyCech X A U)


def plusdenom: AlgebraicTopology.AlternatingFaceMapComplex.obj (drop.obj (CechAugmented X A U)) ⟶
  (ChainComplex.single₀ (Cᵒᵖ ⥤ ModuleCat A)).obj (point.obj (CechAugmented X A U)) where
    f i:= by
      simp
      let g :=(homotpyEquivLocal X A U V).hom.f i
      simp at g
      sorry



def bidule :HomotopyEquiv (AlgebraicTopology.AlternatingFaceMapComplex.obj (drop.obj (CechAugmented X A U)))
  ((ChainComplex.single₀ (Cᵒᵖ ⥤ ModuleCat A)).obj (point.obj (CechAugmented X A U))) where
    hom := by

      sorry
    inv := sorry
    homotopyHomInvId := sorry
    homotopyInvHomId := sorry




--CategoryTheory.Arrow.AugmentedCechNerve.extraDegeneracy