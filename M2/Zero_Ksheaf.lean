import M2.Ksheaves
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.Limits.Connected

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite

universe u v w

variable {X : Type w } [TopologicalSpace X] [T2Space X]
variable (C : Type u) [Category.{v, u} C]  [HasZeroObject C] [HasZeroMorphisms C]
--the condition of having 0 map is a consequence of having a 0:C but the mathlib page of hasZeroMorphism says it's better to do that
--TODO: improve the example for the case where there is just a terminal object -> it does not work
noncomputable section



/-
@[simps]
def FTop : (Compacts X)ᵒᵖ ⥤ C where
  obj _ := ⊤_C
  map _ := terminal.from (⊤_ C)

variable (K : Compacts X)

#check (Functor.const ((supSupK_cat K)ᵒᵖ))

def TopKsheaf : Ksheaf X C where
  carrier := FTop C
  ksh1 := terminalIsTerminal
  ksh2 K1 K2:= by
    apply PullbackCone.isLimitAux _ (fun _ => terminal.from _)
    · intro _
      simp_all only [FTop_obj, SquareSuptoInf_pt, SquareSuptoInf_π_app, PullbackCone.π_app_left]
      ext : 1
    · intro s
      simp_all only [FTop_obj, SquareSuptoInf_pt, SquareSuptoInf_π_app, PullbackCone.π_app_right]
      ext : 1
    · intro _ _ _
      simp_all only [FTop_obj, SquareSuptoInf_pt, SquareSuptoInf_π_app]
      ext : 1
  ksh3 := by
    intro K
    exact ⟨fun s => s.ι.app ( op (Nonempty.some (instNonemptySupSupK_cat K))),
    by
      intro s j
      simp [terminal.hom_ext (terminal.from (⊤_ C)) (𝟙 (⊤_ C))]
      --surement faux du coup non
      sorry, by
      intro _ _ hm
      simp [ ← (hm _), terminal.hom_ext (terminal.from (⊤_ C)) (𝟙 (⊤_ C))]⟩-/
--
open ZeroObject Zero

noncomputable section

/-- The constant functor equal to 0-/
@[simps]
def FZero : (Compacts X)ᵒᵖ ⥤ C where-- := 0 does not allow aesop to deduce following facts
  obj _ := 0
  map _ := 0

/--The functor FZero gives rise to a Ksheaf-/
def ZKsheaf : Ksheaf X C where
  carrier := FZero C
  ksh1 := HasZeroObject.zeroIsTerminal
  ksh2 K K' := by
    apply PullbackCone.isLimitAux _ 0
    · intro _
      simp_all only [FZero, Pi.zero_apply, PullbackCone.π_app_left, zero_comp]
      ext : 1
    · intro s
      simp_all only [FZero, Pi.zero_apply, PullbackCone.π_app_right, zero_comp]
      ext : 1
    · intro _ _ _
      apply IsZero.eq_zero_of_tgt (isZero_zero _)
  ksh3 K := by
    constructor
    · intro _ _
      exact HasZeroObject.from_zero_ext_iff.mpr trivial
    · intro _ _ _
      exact HasZeroObject.from_zero_ext_iff.mpr trivial
    · intro _
      exact 0

instance : Inhabited (Ksheaf X C) where
  default := ZKsheaf C

#check colimit.isoColimitCocone

#lint
