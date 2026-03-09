import M2.Propre.Topology
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Order.CompleteLattice.MulticoequalizerDiagram

universe w v u

open Topology CategoryTheory TopologicalSpace Opposite Limits

variable {A : Type u} [Category.{v} A] {X : Type w} [TopologicalSpace X]

variable (A X) in
abbrev KPresheaf := (Compacts X)ᵒᵖ ⥤ A

namespace KPresheaf

@[simps]
def coconeOfCompacts (P : KPresheaf A X) (K : Compacts X) :
    Cocone ((Subtype.mono_coe K.compactNhds).functor.op ⋙ P) where
  pt := P.obj (op K)
  ι.app K' := P.map (homOfLE (Compacts.subset_of_mem_compactNhds K'.unop.prop)).op
  ι.naturality _ _ _ := by
    dsimp
    rw [Category.comp_id, ← Functor.map_comp]
    rfl

def coconeOfClosureOfOpens (P : KPresheaf A X) (K : Compacts X)  := Cocone.whisker K.mono_orcNhds_to_compactNhds.functor.op <|  P.coconeOfCompacts K

variable [T2Space X]

/-noncomputable def truc (P : KPresheaf X A) (K : Compacts X) : IsColimit (P.coconeOfClosureOfOpens K) ≃ IsColimit (P.coconeOfCompacts K) := Functor.Final.isColimitWhiskerEquiv _ _-/

noncomputable def mapOfOpenClosure (P : KPresheaf A X) (K : Compacts X) (h : (IsColimit (P.coconeOfCompacts K))) {G : (K.openrelativelycompactNhds)ᵒᵖ ⥤ A} (t : Cocone G) (α : (K.mono_orcNhds_to_compactNhds.functor.op ⋙ (Subtype.mono_coe K.compactNhds).functor.op ⋙ P) ⟶ G) : P.obj (op K) ⟶ t.pt := ((Functor.Final.isColimitWhiskerEquiv _ _).invFun h ).map t α


noncomputable def hom_K_ext (P : KPresheaf A X) {K : Compacts X} (h : (IsColimit (P.coconeOfCompacts K))) {W : A} {f f' : P.obj (op K) ⟶ W} (w : ∀ V, (P.coconeOfClosureOfOpens K).ι.app V ≫ f = (P.coconeOfClosureOfOpens K).ι.app V ≫ f' ): f = f' := ((Functor.Final.isColimitWhiskerEquiv _ _).invFun h ).hom_ext w

structure IsKSheaf (P : KPresheaf A X) : Prop where
  nonempty_isTerminal : Nonempty (IsTerminal (P.obj (op ⊥)))
  isPullback {K₁ K₂ K₃ K₄ : Compacts X} (h : Lattice.BicartSq K₁ K₂ K₃ K₄) :
    IsPullback (P.map ((homOfLE h.le₃₄).op)) (P.map ((homOfLE h.le₂₄).op))
      (P.map ((homOfLE h.le₁₃).op)) (P.map ((homOfLE h.le₁₂).op))
  nonempty_isColimit_coconeOfCompacts (K : Compacts X) :
      Nonempty (IsColimit (P.coconeOfCompacts K))

end KPresheaf

variable [T2Space X]

variable (X A) in
structure KSheaf where
  val : KPresheaf A X
  cond : KPresheaf.IsKSheaf val


namespace Ksheaf

noncomputable def mapOfOpenClosure (P : KSheaf A X) (K : Compacts X) {G : (K.openrelativelycompactNhds)ᵒᵖ ⥤ A} (t : Cocone G) (α : (K.mono_orcNhds_to_compactNhds.functor.op ⋙ (Subtype.mono_coe K.compactNhds).functor.op ⋙ P.val) ⟶ G) : P.val.obj (op K) ⟶ t.pt := ((Functor.Final.isColimitWhiskerEquiv _ _).invFun (Classical.choice <| P.cond.nonempty_isColimit_coconeOfCompacts K) ).map t α


noncomputable def hom_K_ext (P : KSheaf A X) {K : Compacts X}  {W : A} {f f' : P.val.obj (op K) ⟶ W} (w : ∀ V, (P.val.coconeOfClosureOfOpens K).ι.app V ≫ f = (P.val.coconeOfClosureOfOpens K).ι.app V ≫ f' ): f = f' := ((Functor.Final.isColimitWhiskerEquiv _ _).invFun (Classical.choice <| P.cond.nonempty_isColimit_coconeOfCompacts K)).hom_ext w

instance : Category (KSheaf A X) :=  InducedCategory.instCategory (F := fun x => x.val)

#min_imports
