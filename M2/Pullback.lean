import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Sheaves.Functors
import M2.alpha_K_sheaf

universe u v w

open CategoryTheory Limits TopologicalSpace Compacts Opposite Functor TopCat

variable {X Y : Type w} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]

variable {f : X → Y} (Cf : Continuous f)

variable {C : Type u} [Category.{v, u} C]

def imageCompact : Compacts X ⥤ Compacts Y where
  obj K := Compacts.map f Cf K
  map i := homOfLE ( by
    intro a ha
    rcases ha with ⟨x, hx1, hx2⟩
    use x
    constructor
    apply leOfHom i
    repeat assumption)

--variable (hf : Injective f)

def KsheafPullback (F:Ksheaf Y C ) : Ksheaf X C where
  carrier := ((imageCompact Cf).op).comp F.carrier
  ksh1 := sorry
  ksh2 := by
    sorry
  ksh3 := by
    sorry
