import M2.Propre.alpha
import M2.Propre.colimit
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import M2.forceColimW
import Mathlib

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite TopCat

universe u v w

section

variable (X : Type u) (Y : Type v) [Preorder X] [Preorder Y]

def ProdPreorder : Type (max u v) := X × Y

instance : Category (ProdPreorder X Y) := CategoryTheory.prod' X Y

instance : Preorder (ProdPreorder X Y) := Prod.instPreorder

instance [IsCofilteredOrEmpty X] [IsCofilteredOrEmpty Y] : IsCofilteredOrEmpty (ProdPreorder X Y) := instIsCofilteredOrEmptyProd


/- ça n'y est même pas avec IsCodirectedOrder <| X × Y
instance [IsCodirectedOrder X] [IsCodirectedOrder Y] : IsCodirectedOrder <| ProdPreorder X Y := by
  constructor
  intro a b
  obtain ⟨c1,h1⟩ := exists_le_le a.1 b.1
  obtain ⟨c2,h2⟩ := exists_le_le a.2 b.2
  use ⟨c1,c2⟩
  constructor
  exact ⟨h1.1,h2.1⟩
  exact ⟨h1.2,h2.2⟩-/

@[simps]
def Monotone.functor_prod {X Y Z: Type*} [Preorder X] [Preorder Y] [Preorder Z] (f : X × Y → Z ) (h : Monotone f) : ProdPreorder X Y ⥤ Z where
obj := f
map {a b } i := homOfLE (h ⟨leOfHom i.1, leOfHom i.2⟩)

theorem Monotone.initial_functorProd_iff {X Y Z : Type*} [Preorder X] [Preorder Y] [Preorder Z] [IsCodirectedOrder X] [IsCodirectedOrder Y] {f : X × Y → Z} (hf : Monotone f) : hf.functor_prod.Initial ↔ ( ∀ z, ∃ xy, f xy ≤ z) := by
  rw [Functor.initial_iff_of_isCofiltered]
  constructor
  · intro ⟨ho,hm⟩ z
    obtain ⟨c, ⟨hc⟩⟩ := ho z
    exact ⟨c, leOfHom hc⟩
  · intro h
    constructor
    · intro d
      obtain ⟨xy,hxy⟩ := h d
      exact ⟨xy, ⟨homOfLE hxy⟩⟩
    · intro _ c _ _
      exact ⟨c, 𝟙 _, rfl⟩

end


noncomputable section

variable {A : Type u} [Category.{v, u} A] [HasLimitsOfSize.{w, w, v,u} A] [HasColimitsOfSize.{w, w, v, u} A] [AB5OfSize.{w, w, v, u} A]
variable {X : Type w} [TopologicalSpace X] [T2Space X]

variable (F : Presheaf A (of X)) {K1 K2 K3 K4: Compacts X} (h : Lattice.BicartSq K1 K2 K3 K4)

def inter : K2.openNhds × K3.openNhds → K1.openNhds := fun U ↦ ⟨U.1.val ⊓ U.2.val, Set.Subset.trans (le_inf h.le₁₂ h.le₁₃) (inf_le_inf U.1.property U.2.property)⟩

lemma inter_mono : Monotone (inter h) := fun _ _ h ↦ Subtype.mk_le_mk.2 (inf_le_inf h.1 h.2)

instance : (inter_mono h).functor_prod.Initial := by
  apply (Monotone.initial_functorProd_iff _ ).mpr
  intro U
  let FK1 := nhdsSet K2.carrier
  let FK2 := nhdsSet K3.carrier

  have : U.1.carrier ∈ (nhdsSet K2.carrier) ⊓ (nhdsSet K3.carrier) := by
    rw [← IsCompact.nhdsSet_inter_eq K2.isCompact' K3.isCompact']
    apply (IsOpen.mem_nhdsSet _).mpr
    apply Set.Subset.trans _ U.property
    apply subset_of_eq
    rw [← h.inf_eq]
    simp only [carrier_eq_coe, coe_inf]
    exact U.val.is_open'

  let h := (Filter.HasBasis.mem_iff (Filter.HasBasis.inf (hasBasis_nhdsSet _) (hasBasis_nhdsSet _))).1 this

  let V := h.choose
  obtain ⟨⟨hV1,hV2⟩,hV3⟩ := h.choose_spec

  use ⟨⟨⟨V.1, hV1.1⟩, hV1.2⟩, ⟨⟨V.2, hV2.1⟩, hV2.2⟩⟩
  exact hV3

def union : K2.openNhds × K3.openNhds → K4.openNhds := fun U ↦ ⟨U.1.val ⊔ U.2.val, by
    apply Set.Subset.trans _ (sup_le_sup U.1.property U.2.property)
    --pas beau du tout
    apply subset_of_eq
    rw [← h.sup_eq]
    simp only [carrier_eq_coe, coe_sup, Set.sup_eq_union]⟩

lemma union_mono : Monotone (union h) := fun _ _ h ↦ Subtype.mk_le_mk.2 (sup_le_sup h.1 h.2)

instance : (union_mono h).functor_prod.Initial := by
  apply (Monotone.initial_functorProd_iff _ ).mpr
  intro U
  use ⟨⟨U.val, Set.Subset.trans h.le₂₄ U.property⟩, ⟨U.val, Set.Subset.trans h.le₃₄ U.property⟩⟩
  exact Subtype.mk_le_mk.2 <| sup_le (le_refl _) (le_refl _)

variable (K1 K2) in
@[simps!]
def forgetLeft : K1.openNhds × K2.openNhds ⥤ Opens X := (CategoryTheory.Prod.fst K1.openNhds K2.openNhds) ⋙ (Subtype.mono_coe K1.openNhds).functor

variable (K1 K2) in
@[simps!]
def forgetRight : K1.openNhds × K2.openNhds ⥤ Opens X := (CategoryTheory.Prod.snd K1.openNhds K2.openNhds) ⋙ (Subtype.mono_coe K2.openNhds).functor

@[simps!]
def DiagO : WalkingCospan ⥤ (K2.openNhds × K3.openNhds)ᵒᵖ ⥤ (Opens X)ᵒᵖ := cospan (X := (forgetLeft K2 K3).op) (Y := (forgetRight K2 K3).op) (Z := ((inter_mono h).functor_prod ⋙ (Subtype.mono_coe K1.openNhds).functor).op) (NatTrans.op ⟨fun U ↦ homOfLE (inf_le_left ),by aesop_cat⟩) (NatTrans.op ⟨fun U ↦ homOfLE (inf_le_right),by aesop_cat⟩)

@[simps!]
def DiagBis : WalkingCospan ⥤ (K2.openNhds × K3.openNhds)ᵒᵖ  ⥤ A := ((Functor.whiskeringRight WalkingCospan _ _).obj ((Functor.whiskeringRight (K2.openNhds × K3.openNhds)ᵒᵖ _ _).obj F)).obj (DiagO h)

@[simps!]
def Diag : WalkingCospan ⥤ (K2.openNhds × K3.openNhds)ᵒᵖ  ⥤ A := cospan ((DiagBis F h).map WalkingCospan.Hom.inl) ((DiagBis F h).map WalkingCospan.Hom.inr)

def LjD : Cone (Diag F h) := by
  apply PullbackCone.mk (W := ((union_mono h).functor_prod ⋙ (Subtype.mono_coe K4.openNhds).functor).op ⋙ F) (eq := _)
  · apply Functor.whiskerRight
    exact NatTrans.op ⟨fun U ↦ homOfLE (le_sup_left),by aesop_cat⟩
  · apply Functor.whiskerRight
    exact NatTrans.op ⟨fun U ↦ homOfLE (le_sup_right),by aesop_cat⟩
  · ext; simp; rw [← F.map_comp, ← F.map_comp]; rfl

@[simps]
def CategoryTheory.Limits.Cone.eval {J K C : Type*} [Category J] [Category K] [Category C] { F : J ⥤ K ⥤ C } (c : Cone F) (U : K) : Cone (F.flip.obj U) where
  pt := c.pt.obj U
  π.app j := (c.π.app j).app U
  π.naturality {_ _} _:= by
    dsimp
    rw [← NatTrans.comp_app, c.w]
    simp

@[simps]
def CategoryTheory.Limits.Cocone.eval {J K C : Type*} [Category J] [Category K] [Category C] { F : J ⥤ K ⥤ C } (c : Cocone F) (U : K) : Cocone (F.flip.obj U) where
  pt := c.pt.obj U
  ι.app j := (c.ι.app j).app U
  ι.naturality {_ _} _:= by
    dsimp
    rw [← NatTrans.comp_app, c.w]
    simp

attribute [local simp] inter
def hLjD (F : Sheaf A (of X)): IsLimit (LjD F.obj h) := by
  let i (U) : cospan (F.obj.map (homOfLE (inf_le_left (a := U.unop.1.val) (b := U.unop.2.val))).op) (F.obj.map (homOfLE inf_le_right).op) ≅ (Diag F.obj h).flip.obj U:= cospanIsoMk (Iso.refl _ ) (Iso.refl _ ) (Iso.refl _ )
  let c (s: Cone (Diag F.obj h)) (U: (↑K2.openNhds × ↑K3.openNhds)ᵒᵖ) := (Cone.postcomposeEquivalence (i U )).inverse.obj (s.eval U)

  refine PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_
  · intro s
    exact ⟨fun U ↦ (Sheaf.isLimitPullbackCone F U.unop.1.val U.unop.2.val).lift (c s U), set_option backward.isDefEq.respectTransparency false in by
    intro U V f

    apply PullbackCone.IsLimit.hom_ext (F.isLimitPullbackCone ↑(unop V).1 ↑(unop V).2)
    ·
      simp
      --refaire plus propre

      let fac := (F.isLimitPullbackCone ↑(unop V).1 ↑(unop V).2).fac (c s V) .left
      dsimp at fac
      rw [fac]

      rw [← F.obj.map_comp]
      let fac := (F.isLimitPullbackCone ↑(unop U).1 ↑(unop U).2).fac (c s U) .left
      simp [c,i] at fac
      simp [c,i]
      rw [← fac]
      rw [← F.obj.map_comp,Category.assoc,← F.obj.map_comp];rfl
    · simp

      let fac := (F.isLimitPullbackCone ↑(unop V).1 ↑(unop V).2).fac (c s V) .right
      dsimp at fac
      rw [fac]

      rw [← F.obj.map_comp]
      let fac := (F.isLimitPullbackCone ↑(unop U).1 ↑(unop U).2).fac (c s U) .right
      simp [c,i] at fac
      simp [c,i]
      rw [← fac]
      rw [← F.obj.map_comp, Category.assoc, ← F.obj.map_comp];rfl⟩
  · intro s
    apply NatTrans.ext
    ext U
    simp
    let fac := (F.isLimitPullbackCone ↑(unop U).1 ↑(unop U).2).fac (c s U) .left
    simp [c,i] at fac
    rw [← fac]
    rfl
  · intro s
    apply NatTrans.ext
    ext U
    simp
    let fac := (F.isLimitPullbackCone ↑(unop U).1 ↑(unop U).2).fac (c s U) .right
    simp [c,i] at fac
    rw [← fac]
    rfl
  · intro s m hml hmr
    apply NatTrans.ext
    ext U
    apply (F.isLimitPullbackCone ↑(unop U).1 ↑(unop U).2).uniq (c s U)
    rintro (x|x|x)
    · simp [c, i]
      rw [← congr_fun (NatTrans.ext_iff.1 hml) U]
      dsimp
      rw [← F.obj.map_comp, Category.assoc, ← F.obj.map_comp];rfl
    · simp [c, i]
      rw [← congr_fun (NatTrans.ext_iff.1 hml) U]
      rfl
    · simp [c, i]
      rw [← congr_fun (NatTrans.ext_iff.1 hmr) U]
      rfl

@[simps]
def LkD : Cocone (Diag F h).flip where
  pt := cospan (F.toKPresheafFunctorObjMap (homOfLE h.le₁₂)) (F.toKPresheafFunctorObjMap (homOfLE h.le₁₃))
  ι.app U := by
    refine cospanHomMk ?_ ?_ ?_ ?_ ?_
    · exact  F.ιToKPresheafFunctorObjObj ⟨_,by
      apply Set.subset_inter
      exact Set.Subset.trans h.le₁₂ U.unop.1.property
      exact Set.Subset.trans h.le₁₃ U.unop.2.property⟩
    · exact  F.ιToKPresheafFunctorObjObj ⟨_, U.unop.1.property⟩
    · exact  F.ιToKPresheafFunctorObjObj ⟨_, U.unop.2.property⟩
    · simp
      unfold TopCat.Presheaf.ιToKPresheafFunctorObjObj
      forceColimW
      exact op (homOfLE (Subtype.mk_le_mk.mpr inf_le_left))
    · simp
      unfold TopCat.Presheaf.ιToKPresheafFunctorObjObj
      forceColimW
      exact op (homOfLE (Subtype.mk_le_mk.mpr inf_le_right))
  ι.naturality {U V} i := by
    ext (x|x|x)
    · simp [TopCat.Presheaf.ιToKPresheafFunctorObjObj]
      forceColimW
      exact op (homOfLE (Subtype.mk_le_mk.mpr (inf_le_inf (leOfHom i.unop.1) (leOfHom i.unop.2))))
    · simp [TopCat.Presheaf.ιToKPresheafFunctorObjObj]
      forceColimW
      exact op (homOfLE (Subtype.mk_le_mk.mpr (leOfHom i.unop.1)))
    · simp [TopCat.Presheaf.ιToKPresheafFunctorObjObj]
      forceColimW
      exact op (homOfLE (Subtype.mk_le_mk.mpr (leOfHom i.unop.2)))

--set_option backward.isDefEq.respectTransparency false in
def hLkD : IsColimit (LkD F h) where
  desc s := by
    refine cospanHomMk ?_ ?_ ?_ ?_ ?_
    · exact (Functor.Final.colimitCoconeComp (inter_mono h).functor_prod.op ⟨_, F.isColimitToKPresheafFunctorObjObjCocone K1⟩ ).isColimit.desc (s.eval .one)
    · exact (Functor.Final.colimitCoconeComp ((CategoryTheory.Prod.fst K2.openNhds K3.openNhds).op) ⟨_, F.isColimitToKPresheafFunctorObjObjCocone K2⟩ ).isColimit.desc (s.eval .left)
    · exact (Functor.Final.colimitCoconeComp ((CategoryTheory.Prod.snd K2.openNhds K3.openNhds).op) ⟨_, F.isColimitToKPresheafFunctorObjObjCocone K3⟩ ).isColimit.desc (s.eval .right)
    · apply (Functor.Final.colimitCoconeComp ((CategoryTheory.Prod.fst K2.openNhds K3.openNhds).op) ⟨_, F.isColimitToKPresheafFunctorObjObjCocone K2⟩ ).isColimit.hom_ext

      intro U
      dsimp
      let hyp := ((Functor.Final.colimitCoconeComp ((CategoryTheory.Prod.fst K2.openNhds K3.openNhds).op) ⟨_, F.isColimitToKPresheafFunctorObjObjCocone K2⟩ ).isColimit.fac) (s.eval .left) U
      dsimp at hyp
      slice_rhs 1 2 => rw [hyp]

      let hyp:= (s.ι.app U).naturality WalkingCospan.Hom.inl
      dsimp at hyp
      rw [← hyp]

      let hyp := (Functor.Final.colimitCoconeComp (inter_mono h).functor_prod.op ⟨_, F.isColimitToKPresheafFunctorObjObjCocone K1⟩ ).isColimit.fac (s.eval .one) U

      dsimp at hyp
      rw [← hyp]

      rw [← Category.assoc, ← Category.assoc]
      apply eq_whisker
      simp
      unfold TopCat.Presheaf.ιToKPresheafFunctorObjObj
      forceColimW
      exact op (homOfLE (Subtype.mk_le_mk.2 inf_le_left))
    · apply (Functor.Final.colimitCoconeComp ((CategoryTheory.Prod.snd K2.openNhds K3.openNhds).op) ⟨_, F.isColimitToKPresheafFunctorObjObjCocone K3⟩ ).isColimit.hom_ext

      intro U
      dsimp
      let hyp := ((Functor.Final.colimitCoconeComp ((CategoryTheory.Prod.snd K2.openNhds K3.openNhds).op) ⟨_, F.isColimitToKPresheafFunctorObjObjCocone K3⟩ ).isColimit.fac) (s.eval .right) U
      dsimp at hyp
      slice_rhs 1 2 => rw [hyp]

      let hyp:= (s.ι.app U).naturality WalkingCospan.Hom.inr
      dsimp at hyp
      rw [← hyp]

      let hyp := (Functor.Final.colimitCoconeComp (inter_mono h).functor_prod.op ⟨_, F.isColimitToKPresheafFunctorObjObjCocone K1⟩ ).isColimit.fac (s.eval .one) U

      dsimp at hyp
      rw [← hyp]

      rw [← Category.assoc, ← Category.assoc]
      apply eq_whisker
      simp
      unfold TopCat.Presheaf.ιToKPresheafFunctorObjObj
      forceColimW
      exact op (homOfLE (Subtype.mk_le_mk.2 inf_le_right))
  fac s U := by
    ext x
    match x with
      |.one => exact (Functor.Final.colimitCoconeComp (inter_mono h).functor_prod.op ⟨_, F.isColimitToKPresheafFunctorObjObjCocone K1⟩ ).isColimit.fac (s.eval .one) U
      |.left => exact (Functor.Final.colimitCoconeComp ((CategoryTheory.Prod.fst K2.openNhds K3.openNhds).op) ⟨_, F.isColimitToKPresheafFunctorObjObjCocone K2⟩ ).isColimit.fac (s.eval .left) U
      |.right => exact (Functor.Final.colimitCoconeComp ((CategoryTheory.Prod.snd K2.openNhds K3.openNhds).op) ⟨_, F.isColimitToKPresheafFunctorObjObjCocone K3⟩ ).isColimit.fac (s.eval .right) U
  uniq s m hm := by
    ext x
    match x with
      |.one =>
        apply (Functor.Final.colimitCoconeComp (inter_mono h).functor_prod.op ⟨_, F.isColimitToKPresheafFunctorObjObjCocone K1⟩ ).isColimit.uniq (s.eval .one)
        intro U
        exact funext_iff.1 (NatTrans.ext_iff.1 (hm U)) .one
      |.left =>
        apply (Functor.Final.colimitCoconeComp ((CategoryTheory.Prod.fst K2.openNhds K3.openNhds).op) ⟨_, F.isColimitToKPresheafFunctorObjObjCocone K2⟩ ).isColimit.uniq (s.eval .left)
        intro U
        exact funext_iff.1 (NatTrans.ext_iff.1 (hm U)) .left
      |.right =>
        apply (Functor.Final.colimitCoconeComp ((CategoryTheory.Prod.snd K2.openNhds K3.openNhds).op) ⟨_, F.isColimitToKPresheafFunctorObjObjCocone K3⟩ ).isColimit.uniq (s.eval .right)
        intro U
        exact funext_iff.1 (NatTrans.ext_iff.1 (hm U)) .right


def LkLjD : Cocone (LjD F h).pt := (Functor.Final.colimitCoconeComp (union_mono h).functor_prod.op ⟨_, F.isColimitToKPresheafFunctorObjObjCocone K4⟩ ).cocone

def hLkLjD : IsColimit (LkLjD F h) := (Functor.Final.colimitCoconeComp (union_mono h).functor_prod.op ⟨_, F.isColimitToKPresheafFunctorObjObjCocone K4⟩ ).isColimit

def LjLkD : Cone (LkD F h).pt := limit.cone _

def hLjLkD : IsLimit (LjLkD F h) := limit.isLimit _

def CategoryTheory.Limits.ConeMorphism.iso_of_iso_hom {C D : Type*} [Category C] [Category D] {F: Functor C D} {s t : Cone F} (τ : s ⟶ t) (h : IsIso τ.hom) : s ≅ t  := by
  have : IsIso τ := CategoryTheory.Limits.Cone.cone_iso_of_hom_iso τ
  apply asIso τ

namespace TopCat.Sheaf

variable [LocallyCompactSpace X]

open TopCat.Presheaf

attribute [local simp] union
--variable (F : Sheaf A (of X))
set_option backward.isDefEq.respectTransparency false in
attribute [local simp ] IsColimit.coconePointUniqueUpToIso IsLimit.conePointUniqueUpToIso in
def toSheaf [AB5OfSize.{w, w, v, u} A]: Sheaf A (of X) ⥤ KSheaf A (of X) := by
  apply ObjectProperty.lift _ (Sheaf.forget A (of X) ⋙ toKPresheafFunctor)
  intro F
  constructor
  · apply Nonempty.intro
    have : IsTerminal (((Subtype.mono_coe (⊥ : Compacts X).openNhds).functor.op ⋙ (forget A (of X)).obj F).obj (op (⊥ : (⊥ : Compacts X).openNhds ))) := by
      apply Sheaf.isTerminalOfBotCover F (⊥ : Opens X)
      intro _ h
      rcases h
    apply IsTerminal.ofIso this
    apply @asIso _ _ _ _ (((forget A (of X)).obj F).ιToKPresheafFunctorObjObj (⊥ : (⊥ : Compacts X).openNhds )) (by
      apply isIso_ι_of_isTerminal _ _
      apply IsInitial.op
      exact isInitialElemOpensOpenNhdsBot)
  · intro K1 K2 K3 K4 h
    simp
    set F2 := (forget A (of X)).obj F
    constructor
    · apply Nonempty.intro
      apply (IsLimitConeOfColimF (LjD F2 h) (LkD F2 h) (LkLjD F2 h) (LjLkD F2 h) (hLjD h F) (hLkD F2 h) (hLkLjD F2 h) (hLjLkD F2 h)).ofIsoLimit
      refine CategoryTheory.Limits.ConeMorphism.iso_of_iso_hom ?_ ?_
      · exact ⟨𝟙 _, by
          intro j
          apply (Functor.Final.colimitCoconeComp (union_mono h).functor_prod.op ⟨_, F2.isColimitToKPresheafFunctorObjObjCocone K4⟩ ).isColimit.hom_ext
          intro U
          dsimp [limColimFPtIsoColimLimFPt]
          let fac : F2.ιToKPresheafFunctorObjObj ((union h) (unop U)) ≫ (hLkLjD F2 h).desc (colimit.cocone (LjD F2 h).pt) = colimit.ι (LjD F2 h).pt U := (hLkLjD F2 h).fac (colimit.cocone (LjD F2 h).pt) U
          dsimp [union] at fac

          slice_rhs 1 2 => rw [fac]
          simp [LjD]
          match j with
            |.one =>
              simp
              -- ça c'est à mieux faire du coup
              unfold ιToKPresheafFunctorObjObj
              forceColimW
              · exact op ( homOfLE ( Subtype.mk_le_mk.2 inf_right_le_sup_right))
              · rw [← F2.map_comp]; rfl
            |.left =>
              simpa using (Presheaf.toKPresheafFunctorObjObj_w  F2 (op ( homOfLE ( Subtype.mk_le_mk.2 le_sup_left)))).symm
            |.right =>
              simpa using (Presheaf.toKPresheafFunctorObjObj_w  F2 (op ( homOfLE ( Subtype.mk_le_mk.2 le_sup_right)))).symm
          constructor
          rw [← toKPresheafFunctorObjMap_comp, ← toKPresheafFunctorObjMap_comp]
          rfl⟩
      · use 𝟙 _
        aesop_cat
  · intro K
    apply Nonempty.intro
    set F2 := (forget A (of X) ).obj F
    set G := (Subtype.mono_coe K.compactNhds ).functor.op ⋙ (forget A (of X) ⋙ toKPresheafFunctor).obj F



    refine (IsColimit.extendIso ((cEx K).colimOfColim_iso_colim (G) ((Subtype.mono_coe _).functor.op  ⋙ F2) ?_ ?_).hom ( colimit.isColimit _)).ofIsoColimit ?_
    · intro L
      refine ⟨_,isColimitToKPresheafFunctorObjObjCocone _ L.unop.val⟩
    · apply eqToIso
      apply CategoryTheory.Functor.ext
      · intro L M f
        apply toKPresheafFunctorObjObj_hom_ext
        intro U
        simp
        erw [F2.map_id, Category.id_comp]
        simp [G]
        rfl

      · intro L
        rfl

    · refine Cocone.ext ?_ ?_
      · simp
        exact IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (isColimitToKPresheafFunctorObjObjCocone _ K)
      · intro L
        apply toKPresheafFunctorObjObj_hom_ext
        intro U

        simp [ιToKPresheafFunctorObjObj,G]

        simp [G,F2]
        simp [UnionCat.CoconeF.colimOfColim_iso_colim, UnionCat.CoconeF.colim2]



        simp [UnionCat.CoconeF.colimOfColim_iso_colim, cEx, IEx,iEx ]



        sorry


#min_imports
