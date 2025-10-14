import M2.Ksheaves

open CategoryTheory Limits TopologicalSpace Compacts Opposite

universe u v w

variable {X :Type w} [TopologicalSpace.{w} X] [T2Space.{w} X]
variable (K : Compacts X)

variable {C : Type u} [Category.{v, u} C]
variable (F : (Compacts X)ᵒᵖ ⥤ C) (G : Ksheaf C X)
