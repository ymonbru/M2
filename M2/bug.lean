import Mathlib

open CategoryTheory Limits TopologicalSpace Compacts Opposite Functor TopCat

universe u v

class myQuiver (V : Type ) where
  Hom : V → V → Sort

class myCategoryStruct (obj : Type ) : Type  extends myQuiver obj where
  /-- The identity morphism on an object. -/
  id : ∀ X : obj, Hom X X
  /-- Composition of morphisms in a category, written `f ≫ g`. -/
  comp : ∀ {X Y Z : obj}, (Hom X Y) → (Hom Y Z) → (Hom X Z)

class myCategory (obj : Type ) : Type  extends myCategoryStruct obj where /-- Identity morphisms are left identities for composition. -/
  id_comp : ∀ {X Y : obj} (f : Hom X Y), (comp (id X)  f ) = f := by aesop_cat
  /-- Identity morphisms are right identities for composition. -/
  comp_id : ∀ {X Y : obj} (f : X ⟶ Y), f ≫ 𝟙 Y = f := by aesop_cat
  /-- Composition in a category is associative. -/
  assoc : ∀ {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z), (f ≫ g) ≫ h = f ≫ g ≫ h := by
    aesop_cat


variable (B : Type ) [Category B]

variable (G : B ⥤ B)


lemma truc : G = G := by
  apply CategoryTheory.Functor.ext --(h_map := ?_)
    --sorry
  intro U V f
  apply Functor.congr_hom
