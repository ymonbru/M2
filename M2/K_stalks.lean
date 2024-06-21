import Mathlib
import Mathlib.Topology.Separation

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite

variable (X) [TopologicalSpace X] [T2Space X]
variable (p:X) --(K:Compacts X)
variable (F:(Compacts X)ᵒᵖ ⥤ Ab)

def pinK : Set (Compacts X) := fun K => (p ∈ K.carrier)

def pinK_cat : Type := FullSubcategory (pinK X p)

instance : Category (pinK_cat X p) := FullSubcategory.category (pinK X p)

def Fres : ((pinK_cat X p)ᵒᵖ) ⥤ Ab := Functor.comp (fullSubcategoryInclusion (pinK X p)).op F

noncomputable section

def stalk : Ab :=colimit (Fres X p F)

def pC: Compacts X:=⟨{p},isCompact_singleton⟩

def Fp_transNat: (Fres X p F) ⟶ ((Functor.const (pinK_cat X p)ᵒᵖ).obj (op (pC X p))).comp F where
app W:= by
  apply F.map
  apply op
  apply homOfLE
  intro x hx
  rw [ Set.eq_of_mem_singleton hx]
  apply (W.unop).property
naturality := by
  intro U V f
  unfold Fres
  simp
  rw [← F.map_comp]
  rfl


def Fp : Cocone (Fres X p F):= Cocone.mk (F.obj (op (pC X p))) ((Fp_transNat X p F)  ≫ ((Functor.constComp _ _ _).hom))

def pC2: (pinK_cat X p):=⟨pC X p,rfl⟩

def FpisCol : IsColimit (Fp X p F) where
  desc := fun s => s.ι.app (op (pC2 X p))
  fac := fun s => fun _ => s.ι.naturality _
  uniq := by
    intro s m hm
    simp
    rw [← hm (op (pC2 X p))]
    unfold Fp Fp_transNat
    simp
    have: F.map { unop := 𝟙 (pC X p) }= 𝟙 (F.obj {unop:=(pC X p)}) :=
      calc F.map { unop := 𝟙 (pC X p) } = F.map (𝟙 {unop := (pC X p)}) := by congr
        _ = 𝟙 F.obj ({unop := (pC X p)}) := by rw [F.map_id]; rfl

    rw [this, @Category.id_comp _ _ (F.obj {unop:=(pC X p)})  _ m]
