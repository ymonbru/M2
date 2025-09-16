import Mathlib

open CategoryTheory AlgebraicGeometry


structure Scheme extends (X : LocallyRingedSpace) where
local_affine :
∀ x : X,
∃ (U : OpenNhds x) (R : CommRingCat),
Nonempty (X.restrict U ≅ Spec.obj (op R))
