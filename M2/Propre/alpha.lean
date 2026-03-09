import M2.Propre.KSheaf
import M2.forceColimW
import Mathlib.Topology.Sheaves.Sheaf

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite TopCat

universe u v w

variable {X : Type w} [TopologicalSpace X]
variable {A : Type u} [Category.{v, u} A] [HasColimitsOfSize.{w, w} A] [HasLimitsOfSize.{w, w} A ]

/-def baseChangeCompactNhds {K L : Compacts X} (h : K.carrier ⊆ L.carrier) : L.compactNhds → K.compactNhds := fun M => ⟨M.1, fun ⟨x,hx⟩ => M.2 ⟨x, h hx ⟩⟩

lemma monoBaseChangeCompactNhds {K L : Compacts X} (h : K.carrier ⊆ L.carrier) : Monotone <| baseChangeCompactNhds h := fun _ _ hyp => fun _ hx => hyp hx-/


def Quiver.Hom.baseChangeOpenNhds {K L : Compacts X} (h : K ⟶ L) : L.openNhds → K.openNhds := fun ⟨U,hU⟩ => ⟨U, fun _ hx => Set.mem_of_subset_of_mem hU (leOfHom h hx)⟩

--@[simp]
lemma truc (K : Compacts X) : (𝟙 K).baseChangeOpenNhds = fun x => x := rfl

lemma monoBaseChangeOpenNhds {K L : Compacts X} (h : K ⟶ L) : Monotone <| h.baseChangeOpenNhds := fun  _ _ hUV _ hx => SetLike.mem_coe.mpr (hUV hx)

namespace TopCat.Presheaf

noncomputable section
variable (F : Presheaf A (of X))

@[simps]
def alphaUpStarObj : (Compacts X)ᵒᵖ ⥤ A where
  obj K := colimit ((Subtype.mono_coe K.unop.openNhds).functor.op ⋙ F)
  map {K L} i := colimit.pre ((Subtype.mono_coe L.unop.openNhds).functor.op ⋙ F) (monoBaseChangeOpenNhds i.unop).functor.op
  map_id _ := by
    apply colimit.hom_ext
    intro
    rw [CategoryTheory.Limits.colimit.ι_pre]
    exact Eq.symm (Category.comp_id _)-- pourquoi ça ne marche pas tout seul?
  map_comp {K L M} f g := by

    apply colimit.hom_ext
    intro U
    rw [colimit.ι_pre]
    --ça il faut le forcer avec une tactique

    let Eforce := (monoBaseChangeOpenNhds f.unop).functor.op
    let Fforce := (Subtype.mono_coe (unop L).openNhds).functor.op ⋙ F
    let kforce := U

    --have : Eforce ⋙ Fforce = (monoBaseChangeOpenNhds (f ≫ g).unop).functor.op ⋙ (Subtype.mono_coe (unop M).openNhds).functor.op ⋙ F := by rfl
    --ici il arrive à identifier Eforce ⋙ Fforce, mais il ne devrait pas en général→ en fait si?
    slice_rhs 1 2 => erw [ colimit.ι_pre Fforce Eforce _]

    unfold Fforce Eforce

    let Eforce := (monoBaseChangeOpenNhds g.unop).functor.op
    let Fforce := (Subtype.mono_coe (unop M).openNhds).functor.op ⋙ F
    let kforce := (monoBaseChangeOpenNhds f.unop).functor.op.obj U

    erw [ colimit.ι_pre Fforce Eforce _]

    rfl

@[simps]
def alphaUpStarNatTrans { F1 F2 : Presheaf A (of X)} (τ : F1 ⟶ F2) : alphaUpStarObj F1 ⟶ alphaUpStarObj F2 where
app K := colimMap <| Functor.whiskerLeft _ τ
naturality K L i:= by
  apply colimit.hom_ext
  intro j
  unfold alphaUpStarObj
  simp
  -- par une tactique
  let Eforce := (alphaUpStarObj._proof_3 i).functor.op
  let Fforce := (alphaUpStarObj._proof_1 L).functor.op ⋙ F1

  slice_lhs 1 2 => erw [colimit.ι_pre Fforce Eforce]
  unfold Fforce Eforce

  --re tactique
  let Eforce := (alphaUpStarObj._proof_3 i).functor.op
  let Fforce := (alphaUpStarObj._proof_1 L).functor.op ⋙ F2

  slice_rhs 2 3 => erw [colimit.ι_pre Fforce Eforce]
  unfold Fforce Eforce

  simp;rfl

def alphaUpStar : Presheaf A (of X) ⥤ KPresheaf A X where
  obj := alphaUpStarObj
  map := alphaUpStarNatTrans
  map_id F := by
    ext
    apply colimit.hom_ext
    intro
    simp
    forceColimW
    · exact 𝟙 _
    · unfold CategoryStruct.id fForce ;simp;rfl


end
