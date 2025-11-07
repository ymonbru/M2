import M2.RCalpha
import M2.KsheafIso
import Mathlib.Topology.Sheaves.Stalks

import Mathlib

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite TopCat TopCat.Presheaf
open ZeroObject

universe u v w z

variable (C : Type) [Category C]
variable {S : Type } [Preorder S]
variable (a b : S → Prop)

local notation "A" => ObjectProperty.FullSubcategory a
local notation "B" => ObjectProperty.FullSubcategory b

instance : Category A := ObjectProperty.FullSubcategory.category a

instance : Category B := ObjectProperty.FullSubcategory.category b

local notation "BK" => fun K => ObjectProperty.FullSubcategory (fun x => b x ∧ K ≤ x)

instance (K : S) : Category (BK K) := ObjectProperty.FullSubcategory.category (fun x => b x ∧ K ≤ x)

local notation "AU" => fun U => ObjectProperty.FullSubcategory (fun x => b x ∧ x ≤ U)

instance (U : S) : Category (AU U) := ObjectProperty.FullSubcategory.category (fun x => b x ∧ x ≤ U)

variable (K : A) (G : A ⥤ C)
