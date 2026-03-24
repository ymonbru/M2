import M2.Propre.alpha

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite TopCat

universe u v w

variable {A : Type u} [Category.{v, u} A]
variable {X : Type w} [TopologicalSpace X]

namespace TopCat.Sheaf

variable (F : Sheaf A (of X))
