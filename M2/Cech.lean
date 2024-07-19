
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.AlgebraicTopology.CechNerve
import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.AlgebraicTopology.ExtraDegeneracy

open CategoryTheory SimplicialObject.Augmented

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
  naturality A B C:= by
    ext
    simp--a changer
    ext
    simp

def τ:  (Y X U) ⟶ (Sieve.functor R) := (Limits.Sigma.desc (fun (Z:C) => Limits.Sigma.desc fun (f : @U Z) => (tau_Z_f X U Z f)))

/-lemma tau_epi: Epi (τ X U):= by
  constructor
  intros Z u v huv
  apply NatTrans.ext
  ext Z f
  rcases f with ⟨f,Y, g, h, hf1, hf2⟩
  --apply Subtype.ext


  sorry-/

def truc : SplitEpi (Arrow.mk (τ X U)).hom := by
  sorry

def PresheafOfTypeToAMod : (Cᵒᵖ ⥤ Type v) ⥤ Cᵒᵖ ⥤ ModuleCat A := (whiskeringRight Cᵒᵖ  _ _).obj (ModuleCat.free A)

def CechObj : SimplicialObject (Cᵒᵖ ⥤Type v) := (Arrow.mk (τ X U)).cechNerve

def CechObjAugmented : SimplicialObject.Augmented (Cᵒᵖ ⥤Type v) := (Arrow.mk (τ X U)).augmentedCechNerve

def ExtraDegeneracyCechObj : ExtraDegeneracy (CechObjAugmented X U) := Arrow.AugmentedCechNerve.extraDegeneracy (Arrow.mk (τ X U)) (truc _ _)

def Cech : SimplicialObject (Cᵒᵖ ⥤ ModuleCat  A) :=  ((whiskeringRight SimplexCategoryᵒᵖ  (Cᵒᵖ⥤ Type v) (Cᵒᵖ⥤ ModuleCat A)).obj (PresheafOfTypeToAMod A)).obj (CechObj X U)

def CechAugmented : SimplicialObject.Augmented (Cᵒᵖ ⥤ ModuleCat  A) :=((whiskering (Cᵒᵖ ⥤ Type v) (Cᵒᵖ ⥤ ModuleCat A)).obj (PresheafOfTypeToAMod A)).obj (Arrow.mk (τ X U)).augmentedCechNerve

def ExtraDegeneracyCech : ExtraDegeneracy (CechAugmented X A U) := ExtraDegeneracy.map  (ExtraDegeneracyCechObj X U) (PresheafOfTypeToAMod A)

#check ExtraDegeneracy.homotopyEquiv (ExtraDegeneracyCech X A U)






--CategoryTheory.Arrow.AugmentedCechNerve.extraDegeneracy
