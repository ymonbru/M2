import Mathlib

open CategoryTheory Limits

universe u1 v1 u2 v2 u3 v3 u4 v4

variable (A : Type u1) [Category.{v1, u1} A] (B : Type u2) [Category.{v2, u2} B] (C :Type u3) [Category.{v3,u3} C] [IsFiltered B]

variable [HasLimitsOfShape A C]  [HasColimitsOfShape B C]

variable (i : A ⥤ Cat.{v4,u4}) (F : A ⥤ B ⥤ C)

variable (limF : Cone F)

def truc : A ⥤ C where
  obj a := by

    sorry
  map := by sorry
