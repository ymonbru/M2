import Mathlib

open CategoryTheory Limits TopologicalSpace Compacts Opposite Functor TopCat

universe u1 u2 u3 v1 v2 v3
variable {A : Type u2} [Category.{v2, u2} A]

variable (i : A ⥤ Cat.{v3, u3}) (F : Cocone i) (a : A)
variable [HasLimitsOfSize.{max v3 max u2 u3, max u2 u3} F.pt] [HasLimitsOfSize.{v3, u3} F.pt]

#check F.ι.app

#check (i.obj a).α

variable [(a : A) → HasLimitsOfSize.{v3, u3} (i.obj a)]

def cupIa : Type max u2 u3 := ((a : A) × ((i.obj a).α ))

instance : Category (cupIa i) := Sigma.sigma

def FIa : (i.obj a) ⥤ F.pt := F.ι.app a -- pour permetre d'inferer l'existence de limites

@[simps]
def FCupIa : (cupIa i) ⥤ F.pt := CategoryTheory.Sigma.desc F.ι.app

#check limit (FCupIa i F)

def Ia : Type u3 := (i.obj a).α

instance : Category (Ia i a) := Cat.str _


#check limMap

-- pas sur du op mais ça à l'air de marcher mieux
noncomputable def limFIa : Aᵒᵖ ⥤ F.pt where
  obj a := limit (FIa i F a.unop)
  map f := (limit.pre (FIa i F _) (i.map f.unop)) ≫  limMap (Quiver.homOfEq (𝟙 _) (Eq.symm (F.ι.naturality _)) (rfl))
  map_id a:= by
    apply limit.hom_ext
    intro j
    simp

    have : (Quiver.homOfEq (𝟙 _) (Eq.symm (F.ι.naturality _)) (rfl)) = 𝟙 (FIa i F (unop a)) := by
      rfl

      sorry
    have : ((i.map (𝟙 (unop a))).obj j) = j := by
      congr
      simp
    --rw [this]

    erw [ i.map_id a.unop]
    sorry
  map_comp := sorry

#check limit (limFIa)
