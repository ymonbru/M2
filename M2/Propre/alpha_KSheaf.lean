import M2.Propre.alpha
import M2.LimOfColimEqColimOfLim
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import M2.forceColimW
import Mathlib

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite TopCat

universe u v w

noncomputable section

variable {A : Type u} [Category.{v, u} A] [HasLimitsOfSize.{w, w, v,u} A] [HasColimitsOfSize.{w, w, v, u} A] [AB5OfSize.{w, w, v, u} A]
variable {X : Type w} [TopologicalSpace X] [T2Space X]


variable (F : Presheaf A (of X)) {K1 K2 K3 K4: Compacts X} (h : Lattice.BicartSq K1 K2 K3 K4)

@[simps]
def inter : K2.openNhds × K3.openNhds ⥤ K1.openNhds where
  obj U := ⟨U.1.val ⊓ U.2.val, Set.Subset.trans (le_inf h.le₁₂ h.le₁₃) (inf_le_inf U.1.property U.2.property)⟩
  map i := homOfLE (Subtype.mk_le_mk.2 ((inf_le_inf (leOfHom i.1) (leOfHom i.2))))

/-instance : Category (K2.openNhds × K3.openNhds) := by
  exact uniformProd ↑K2.openNhds ↑K3.openNhds
  apply Preorder.smallCategory

lemma truc : uniformProd ↑K2.openNhds ↑K3.openNhds = Preorder.smallCategory _:= by sorry

def inter2 : K2.openNhds × K3.openNhds → K1.openNhds := fun U =>⟨U.1.val ⊓ U.2.val, Set.Subset.trans (le_inf h.le₁₂ h.le₁₃) (inf_le_inf U.1.property U.2.property)⟩
  --map i := homOfLE (Subtype.mk_le_mk.2 ((inf_le_inf (leOfHom i.1) (leOfHom i.2))))

--instance : Preorder (K2.openNhds × K3.openNhds) := by
  --apply?
  --sorry-/




instance : (inter h).Initial := by
  apply (Functor.initial_iff_of_isCofiltered _).mpr
  constructor
  · intro U

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
    exact Nonempty.intro (homOfLE hV3)

  · intro _ c _ _
    use c
    use 𝟙 _
    rfl

@[simps]
def union : K2.openNhds × K3.openNhds ⥤ K4.openNhds where
  obj U := ⟨U.1.val ⊔ U.2.val, by
    apply Set.Subset.trans _ (sup_le_sup U.1.property U.2.property)
    --pas beau du tout
    apply subset_of_eq
    rw [← h.sup_eq]
    simp only [carrier_eq_coe, coe_sup, Set.sup_eq_union]⟩
  map i := homOfLE (Subtype.mk_le_mk.2 (sup_le_sup (leOfHom i.1) (leOfHom i.2)))

instance : (union h).Initial := by
  --probleme de diamand entre produit et prendre la catégorie associée à un préordre

  apply (Functor.initial_iff_of_isCofiltered _).mpr
  constructor
  · intro U
    use ⟨⟨U.val, Set.Subset.trans h.le₂₄ U.property⟩, ⟨U.val, Set.Subset.trans h.le₃₄ U.property⟩⟩

    apply Nonempty.intro
    apply homOfLE
    apply Subtype.mk_le_mk.2
    simp
    apply sup_le
    apply le_refl
    apply le_refl
  · intro _ c _ _
    use c
    use 𝟙 c
    rfl

variable (K1 K2) in
@[simps!]
def forgetLeft : K1.openNhds × K2.openNhds ⥤ Opens X := (CategoryTheory.Prod.fst K1.openNhds K2.openNhds) ⋙ (Subtype.mono_coe K1.openNhds).functor

variable (K1 K2) in
@[simps!]
def forgetRight : K1.openNhds × K2.openNhds ⥤ Opens X := (CategoryTheory.Prod.snd K1.openNhds K2.openNhds) ⋙ (Subtype.mono_coe K2.openNhds).functor

@[simps!]
def DiagO : WalkingCospan ⥤ (K2.openNhds × K3.openNhds)ᵒᵖ ⥤ (Opens X)ᵒᵖ := cospan (X := (forgetLeft K2 K3).op) (Y := (forgetRight K2 K3).op) (Z := (inter h ⋙ (Subtype.mono_coe K1.openNhds).functor).op) (NatTrans.op ⟨fun U => homOfLE (inf_le_left ),by aesop_cat⟩) (NatTrans.op ⟨fun U => homOfLE (inf_le_right),by aesop_cat⟩)

/-def DiagO : (K1.openNhds × K2.openNhds)ᵒᵖ ⥤ WalkingCospan ⥤ (Opens X)ᵒᵖ  where
  obj U := cospan (op (homOfLE inf_le_left): op U.unop.1.val ⟶ op (U.unop.1.val ⊓ U.unop.2.val) ) (op (homOfLE inf_le_right ): op U.unop.2.val ⟶ op (U.unop.1.val ⊓ U.unop.2.val))
  map {U V} i := by
    apply cospanHomMk _ (op i.unop.1) (op i.unop.2)
    apply op
    apply homOfLE
    exact inf_le_inf (leOfHom i.unop.1) (leOfHom i.unop.2)-/

--def Diag : WalkingCospan ⥤ (K1.openNhds × K2.openNhds)ᵒᵖ  ⥤ A := by



--((Functor.whiskeringRight WalkingCospan _ _).obj ((Functor.whiskeringRight (K1.openNhds × K2.openNhds)ᵒᵖ _ _).obj F)).obj (DiagO K1 K2).comp F

@[simps!]
def DiagBis : WalkingCospan ⥤ (K2.openNhds × K3.openNhds)ᵒᵖ  ⥤ A := ((Functor.whiskeringRight WalkingCospan _ _).obj ((Functor.whiskeringRight (K2.openNhds × K3.openNhds)ᵒᵖ _ _).obj F)).obj (DiagO h)

@[simps!]
def Diag : WalkingCospan ⥤ (K2.openNhds × K3.openNhds)ᵒᵖ  ⥤ A := cospan ((DiagBis F h).map WalkingCospan.Hom.inl) ((DiagBis F h).map WalkingCospan.Hom.inr)


/-def LjD : Cone (Diag F K2 K3) where
  pt := (union K2 K3).op ⋙ F
  π:= by
    refine cospanHomMk ?_ ?_ ?_ ?_ ?_
    · apply Functor.whiskerRight
      exact NatTrans.op ⟨fun U => homOfLE (inf_le_sup),by aesop_cat⟩
    · apply Functor.whiskerRight
      exact NatTrans.op ⟨fun U => homOfLE (le_sup_left),by aesop_cat⟩
    · apply Functor.whiskerRight
      exact NatTrans.op ⟨fun U => homOfLE (le_sup_right),by aesop_cat⟩
    repeat ext; simp; rw [← F.map_comp]; rfl-/


def LjD : Cone (Diag F h) := by
  apply PullbackCone.mk (W := (union h ⋙ (Subtype.mono_coe K4.openNhds).functor).op ⋙ F) (eq := _)
  · apply Functor.whiskerRight
    exact NatTrans.op ⟨fun U => homOfLE (le_sup_left),by aesop_cat⟩
  · apply Functor.whiskerRight
    exact NatTrans.op ⟨fun U => homOfLE (le_sup_right),by aesop_cat⟩
  · ext; simp; rw [← F.map_comp, ← F.map_comp]; rfl

@[simps]
def CategoryTheory.Limits.Cone.eval {J K C : Type*} [Category J] [Category K] [Category C] { F : J ⥤ K ⥤ C } (c : Cone F) (U : K) : Cone (F.flip.obj U) where
  pt := c.pt.obj U
  π.app j := (c.π.app j).app U
  π.naturality {_ _} _:= by
    dsimp
    rw [← NatTrans.comp_app, c.w _]
    simp

/-def CategoryTheory.Limits.Cone.evalHom {J K C : Type*} [Category J] [Category K] [Category C] { F : J ⥤ K ⥤ C } (c : Cone F) {U V: K} (i : U ⟶ V) : (Cone.postcompose (F.flip.map i)).obj (c.eval U) ⟶ c.eval V where
  hom := c.pt.map i-/

def i (F : Sheaf A (of X)) : cospan (F.obj.map (homOfLE (inf_le_left (a := U.unop.1.val) (b := U.unop.2.val))).op) (F.obj.map (homOfLE inf_le_right).op) ≅ (Diag F.obj h).flip.obj U:= cospanIsoMk (Iso.refl _ ) (Iso.refl _ ) (Iso.refl _ )

def c (F : Sheaf A (of X)) (s: Cone (Diag F.obj h)) (U: (↑K2.openNhds × ↑K3.openNhds)ᵒᵖ):= (Cone.postcomposeEquivalence (i h F)).inverse.obj (s.eval U)

def hLjD (F : Sheaf A (of X)): IsLimit (LjD F.obj h) := by

  refine PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_
  · intro s
    exact ⟨fun U => (Sheaf.isLimitPullbackCone F U.unop.1.val U.unop.2.val).lift (c h F s U), set_option backward.isDefEq.respectTransparency false in by
    intro U V f

    apply PullbackCone.IsLimit.hom_ext (F.isLimitPullbackCone ↑(unop V).1 ↑(unop V).2)
    · simp
      --refaire plus propre

      let fac := (F.isLimitPullbackCone ↑(unop V).1 ↑(unop V).2).fac (c h F s V) .left
      dsimp at fac
      rw [fac]

      rw [← F.obj.map_comp]
      let fac := (F.isLimitPullbackCone ↑(unop U).1 ↑(unop U).2).fac (c h F s U) .left
      simp [c,i] at fac
      simp [c,i]
      rw [← fac]
      rw [← F.obj.map_comp,Category.assoc,← F.obj.map_comp];rfl
    · simp

      let fac := (F.isLimitPullbackCone ↑(unop V).1 ↑(unop V).2).fac (c h F s V) .right
      dsimp at fac
      rw [fac]

      rw [← F.obj.map_comp]
      let fac := (F.isLimitPullbackCone ↑(unop U).1 ↑(unop U).2).fac (c h F s U) .right
      simp [c,i] at fac
      simp [c,i]
      rw [← fac]
      rw [← F.obj.map_comp,Category.assoc,← F.obj.map_comp];rfl⟩
  · intro s
    apply NatTrans.ext
    ext U
    let fac := (F.isLimitPullbackCone ↑(unop U).1 ↑(unop U).2).fac (c h F s U) .left
    simp [c,i] at fac
    rw [← fac]
    rfl
  · intro s
    apply NatTrans.ext
    ext U
    let fac := (F.isLimitPullbackCone ↑(unop U).1 ↑(unop U).2).fac (c h F s U) .right
    simp [c,i] at fac
    rw [← fac]
    rfl
  · intro s m hml hmr
    apply NatTrans.ext
    ext U
    apply (F.isLimitPullbackCone ↑(unop U).1 ↑(unop U).2).uniq (c h F s U)
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

      apply op
      apply homOfLE
      simp [baseChangeOpenNhds]
      exact Subtype.mk_le_mk.mpr inf_le_left

    · simp [Diag ]
      unfold TopCat.Presheaf.ιToKPresheafFunctorObjObj
      forceColimW

      apply op
      apply homOfLE
      simp [baseChangeOpenNhds]
      exact Subtype.mk_le_mk.mpr inf_le_right
  ι.naturality {U V} i := by
    ext (x|x|x)
    · simp [TopCat.Presheaf.ιToKPresheafFunctorObjObj]
      forceColimW
      apply op
      apply homOfLE
      exact Subtype.mk_le_mk.mpr (inf_le_inf (leOfHom i.unop.1) (leOfHom i.unop.2) )
    · simp [TopCat.Presheaf.ιToKPresheafFunctorObjObj]
      forceColimW
      apply op
      apply homOfLE
      exact Subtype.mk_le_mk.mpr (leOfHom i.unop.1)
    · simp [TopCat.Presheaf.ιToKPresheafFunctorObjObj]
      forceColimW
      apply op
      apply homOfLE
      exact Subtype.mk_le_mk.mpr (leOfHom i.unop.2)

--set_option backward.isDefEq.respectTransparency false in
def hLkD : IsColimit (LkD F h) where
  desc s := by
    refine cospanHomMk ?_ ?_ ?_ ?_ ?_
    · exact (Functor.Final.colimitCoconeComp (inter h).op ⟨_, F.isColimitToKPresheafFunctorObjObjCocone K1⟩ ).isColimit.desc ⟨s.pt.obj WalkingCospan.one, ⟨fun U => (s.ι.app U).app .one,by
        intro _ _ f
        dsimp
        rw [ ← s.w f]
        dsimp [Diag]
        aesop_cat⟩⟩
    · exact (Functor.Final.colimitCoconeComp ((CategoryTheory.Prod.fst K2.openNhds K3.openNhds).op) ⟨_, F.isColimitToKPresheafFunctorObjObjCocone K2⟩ ).isColimit.desc ⟨s.pt.obj WalkingCospan.left, ⟨fun U => (s.ι.app U).app .left, by
        intro _ _ f
        dsimp
        rw [ ← s.w f]
        dsimp [Diag]
        aesop_cat⟩⟩
    · exact (Functor.Final.colimitCoconeComp ((CategoryTheory.Prod.snd K2.openNhds K3.openNhds).op) ⟨_, F.isColimitToKPresheafFunctorObjObjCocone K3⟩ ).isColimit.desc ⟨s.pt.obj WalkingCospan.right, ⟨fun U => (s.ι.app U).app .right, by
        intro U V f
        dsimp
        rw [ ← s.w f]
        dsimp [Diag]
        aesop_cat⟩⟩
    · apply (Functor.Final.colimitCoconeComp ((CategoryTheory.Prod.fst K2.openNhds K3.openNhds).op) ⟨_, F.isColimitToKPresheafFunctorObjObjCocone K2⟩ ).isColimit.hom_ext

      intro U

      dsimp

      --let h := (s.ι.app U).naturality WalkingCospan.Hom.inl
      let hyp := (Functor.Final.colimitCoconeComp (inter h).op ⟨_, F.isColimitToKPresheafFunctorObjObjCocone K1⟩ ).isColimit.fac ⟨s.pt.obj WalkingCospan.one, ⟨fun U => (s.ι.app U).app .one,by
        intro _ _ f
        dsimp
        rw [ ← s.w f]
        dsimp [Diag]
        aesop_cat⟩⟩ U

      dsimp [inter] at hyp
      --unfold inter at hyp

      --rw [h]

      let h := ((Functor.Final.isColimitWhiskerEquiv (CategoryTheory.Prod.fst ↑K2.openNhds ↑K3.openNhds).op
                (F.toKPresheafFunctorObjObjCocone K2)).symm
            (F.isColimitToKPresheafFunctorObjObjCocone K2)).fac ⟨s.pt.obj WalkingCospan.left, ⟨fun U => (s.ι.app U).app .left, by
        intro _ _ f
        dsimp
        rw [ ← s.w f]
        dsimp [Diag]
        aesop_cat⟩⟩ U

      simp at h

      --rw [ h]






      --dsimp
      sorry
    · sorry

def LkLjD : Cocone (LjD F h).pt := (Functor.Final.colimitCoconeComp (union h).op ⟨_, F.isColimitToKPresheafFunctorObjObjCocone K4⟩ ).cocone

def hLkLjD : IsColimit (LkLjD F h) := (Functor.Final.colimitCoconeComp (union h).op ⟨_, F.isColimitToKPresheafFunctorObjObjCocone K4⟩ ).isColimit

def LjLkD : Cone (LkD F h).pt := limit.cone _

def hLjLkD : IsLimit (LjLkD F h) := limit.isLimit _

lemma CategoryTheory.Limits.ConeMorphism.isIso_of_isIso_hom {C D : Type*} [Category C] [Category D] {F: Functor C D} {s t : Cone F} (τ : s ⟶ t) (h : IsIso τ.hom) : IsIso τ := by
  constructor
  obtain ⟨σhom,h1,h2⟩ := h
  exact ⟨⟨σhom,by
    intro _
    rw [← τ.w, ← Category.assoc, h2, Category.id_comp]⟩,⟨by aesop, by aesop⟩⟩

def CategoryTheory.Limits.ConeMorphism.iso_of_iso_hom {C D : Type*} [Category C] [Category D] {F: Functor C D} {s t : Cone F} (τ : s ⟶ t) (h : IsIso τ.hom) : s ≅ t  := by
  have : IsIso τ := isIso_of_isIso_hom τ h
  apply asIso τ

namespace TopCat.Sheaf

open TopCat.Presheaf

--variable (F : Sheaf A (of X))
set_option backward.isDefEq.respectTransparency false in
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
      exact instIsInitialElemOpensOpenNhdsBot)
  · intro K1 K2 K3 K4 h
    simp
    set F2 := (forget A (of X)).obj F
    constructor
    · apply Nonempty.intro

      apply (IsLimitConeOfColimF (LjD F2 h) (LkD F2 h) (LkLjD F2 h) (LjLkD F2 h) (hLjD h F) (hLkD F2 h) (hLkLjD F2 h) (hLjLkD F2 h)).ofIsoLimit

      refine CategoryTheory.Limits.ConeMorphism.iso_of_iso_hom ?_ ?_
      · exact ⟨𝟙 _,by
          intro j
          apply (Functor.Final.colimitCoconeComp (union h).op ⟨_, F2.isColimitToKPresheafFunctorObjObjCocone K4⟩ ).isColimit.hom_ext
          intro U
          simp [limColimFPtIsoColimLimFPt]
          let hyp := (hLkLjD F2 h).fac (colimit.cocone (LjD F2 h).pt) U
          dsimp [LkLjD ] at hyp
          slice_rhs 1 2 => rw [hyp]

          simp [LjD]
          match j with
            |.one =>
              simp
              unfold ιToKPresheafFunctorObjObj
              forceColimW
              exact op ( homOfLE ( Subtype.mk_le_mk.2 inf_right_le_sup_right))
              rw [← F2.map_comp]; rfl
            |.left =>
              simp
              unfold ιToKPresheafFunctorObjObj
              forceColimW
              exact op ( homOfLE ( Subtype.mk_le_mk.2 le_sup_left))
            |.right =>
              simp
              unfold ιToKPresheafFunctorObjObj
              forceColimW
              exact op ( homOfLE ( Subtype.mk_le_mk.2 le_sup_right))
          constructor
          aesop ⟩
      · use 𝟙 _
        aesop_cat
  · intro K
    apply Nonempty.intro
    sorry

#min_imports
