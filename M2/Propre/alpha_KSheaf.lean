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


variable (F : Presheaf A (of X)) (K1 K2 K3 K4: Compacts X) (h : Lattice.BicartSq K1 K2 K3 K4)

@[simps]
def inter : K1.openNhds × K2.openNhds ⥤ Opens X where
  obj U := U.1.val ⊓ U.2.val
  map i := homOfLE (inf_le_inf (leOfHom i.1) (leOfHom i.2))

@[simps!]
def forgetLeft : K1.openNhds × K2.openNhds ⥤ Opens X := (CategoryTheory.Prod.fst K1.openNhds K2.openNhds) ⋙ (Subtype.mono_coe K1.openNhds).functor

@[simps!]
def forgetRight : K1.openNhds × K2.openNhds ⥤ Opens X := (CategoryTheory.Prod.snd K1.openNhds K2.openNhds) ⋙ (Subtype.mono_coe K2.openNhds).functor

@[simps]
def union : K1.openNhds × K2.openNhds ⥤ Opens X where
  obj U := U.1.val ⊔ U.2.val
  map i := homOfLE (sup_le_sup (leOfHom i.1) (leOfHom i.2))

@[simps!]
def DiagO : WalkingCospan ⥤ (K1.openNhds × K2.openNhds)ᵒᵖ ⥤ (Opens X)ᵒᵖ := cospan (X := (forgetLeft K1 K2).op) (Y := (forgetRight K1 K2).op) (Z := (inter K1 K2).op) (NatTrans.op ⟨fun U => homOfLE (inf_le_left ),by aesop_cat⟩) (NatTrans.op ⟨fun U => homOfLE (inf_le_right),by aesop_cat⟩)

/-def DiagO : (K1.openNhds × K2.openNhds)ᵒᵖ ⥤ WalkingCospan ⥤ (Opens X)ᵒᵖ  where
  obj U := cospan (op (homOfLE inf_le_left): op U.unop.1.val ⟶ op (U.unop.1.val ⊓ U.unop.2.val) ) (op (homOfLE inf_le_right ): op U.unop.2.val ⟶ op (U.unop.1.val ⊓ U.unop.2.val))
  map {U V} i := by
    apply cospanHomMk _ (op i.unop.1) (op i.unop.2)
    apply op
    apply homOfLE
    exact inf_le_inf (leOfHom i.unop.1) (leOfHom i.unop.2)-/

@[simps!]
def Diag : WalkingCospan ⥤ (K1.openNhds × K2.openNhds)ᵒᵖ  ⥤ A := ((Functor.whiskeringRight WalkingCospan _ _).obj ((Functor.whiskeringRight (K1.openNhds × K2.openNhds)ᵒᵖ _ _).obj F)).obj (DiagO K1 K2)

def LjD : Cone (Diag F K2 K3) where
  pt := (union K2 K3).op ⋙ F
  π:= by
    refine cospanHomMk ?_ ?_ ?_ ?_ ?_
    · apply Functor.whiskerRight
      exact NatTrans.op ⟨fun U => homOfLE (inf_le_sup),by aesop_cat⟩
    · apply Functor.whiskerRight
      exact NatTrans.op ⟨fun U => homOfLE (le_sup_left),by aesop_cat⟩
    · apply Functor.whiskerRight
      exact NatTrans.op ⟨fun U => homOfLE (le_sup_right),by aesop_cat⟩
    repeat ext; simp; rw [← F.map_comp]; rfl

/-@[simps]
def CategoryTheory.Limits.Cone.eval {J K C : Type*} [Category J] [Category K] [Category C] { F : J ⥤ K ⥤ C } (c : Cone F) (U : K) : Cone (F.flip.obj U) where
  pt := c.pt.obj U
  π.app j := (c.π.app j).app U
  π.naturality {_ _} _:= by
    dsimp
    rw [← NatTrans.comp_app, c.w _]
    simp

def CategoryTheory.Limits.Cone.evalHom {J K C : Type*} [Category J] [Category K] [Category C] { F : J ⥤ K ⥤ C } (c : Cone F) {U V: K} (i : U ⟶ V) : (Cone.postcompose (F.flip.map i)).obj (c.eval U) ⟶ c.eval V where
  hom := c.pt.map i-/




def hLjD (F : Sheaf A (of X)): IsLimit (LjD F.obj K2 K3) where
  lift s := sorry/-⟨fun U =>
      let i : cospan (F.obj.map (homOfLE (inf_le_left (a := U.unop.1.val) (b := U.unop.2.val))).op) (F.obj.map (homOfLE inf_le_right).op) ≅ (Diag F.obj K2 K3).flip.obj U:= cospanIsoMk (Iso.refl _ ) (Iso.refl _ ) (Iso.refl _ )
      let c := (Cone.postcomposeEquivalence i).inverse.obj (s.eval U)
      (Sheaf.isLimitPullbackCone F U.unop.1.val U.unop.2.val).lift c
      --(Sheaf.isLimitPullbackCone F U.unop.1.val U.unop.2.val).lift ((Cone.postcomposeEquivalence (cospanIsoMk (Iso.refl _ ) (Iso.refl _ ) (Iso.refl _ ) :cospan (F.obj.map (homOfLE (inf_le_left (a := U.unop.1.val) (b := U.unop.2.val))).op) (F.obj.map (homOfLE inf_le_right).op) ≅ (Diag F.obj K2 K3).flip.obj U )).inverse.obj (s.eval U))

      ,by
        intro U V f
        let i : cospan (F.obj.map (homOfLE (inf_le_left (a := U.unop.1.val) (b := U.unop.2.val))).op) (F.obj.map (homOfLE inf_le_right).op) ≅ (Diag F.obj K2 K3).flip.obj U:= cospanIsoMk (Iso.refl _ ) (Iso.refl _ ) (Iso.refl _ )
        let c := (Cone.postcomposeEquivalence i).inverse.obj (s.eval U)


        beta_reduce
        apply Eq.trans

        --apply (F.isLimitPullbackCone U.unop.1.val U.unop.2.val).uniq (c.extend (s.pt.map f))


        apply IsLimit.hom_ext (F.isLimitPullbackCone V.unop.1.val V.unop.2.val)
        rintro (j | j |j)
        · simp

          simp [LjD]


          rw [← F.obj.map_comp]

          sorry
        dsimp
        simp
        sorry⟩
    --sorry-/

@[simps]
def LkD : Cocone (Diag F K2 K3).flip where
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

    · simp [Diag, DiagO, ]
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

def hLkD : IsColimit (LkD F K1 K2 K3 K4 h) where
  desc := sorry

def LkLjD : Cocone (LjD F K1 K2).pt := colimit.cocone _

def hLkLjD : IsColimit (LkLjD F K1 K2 ) := colimit.isColimit (LjD F K1 K2).pt


set_option backward.isDefEq.respectTransparency false in
@[simps]
def LjLkD : Cone (LkD F K1 K2 K3 K4 h).pt where
  pt := F.toKPresheafFunctorObjObj K4
  π.app x := match x with
    |.one => F.toKPresheafFunctorObjMap (homOfLE <| h.le₁₂.trans h.le₂₄)
    |.left =>  F.toKPresheafFunctorObjMap (homOfLE <| h.le₂₄)
    |.right =>  F.toKPresheafFunctorObjMap (homOfLE <| h.le₃₄)
  π.naturality {x y} := by
    rintro (f| f| f)
    repeat aesop_cat


def hLjLkD : IsLimit (LjLkD F K1 K2 K3 K4 h) where
  lift s := by
    simp only [LkD ]at s
    #check (F.isColimitToKPresheafFunctorObjObjCocone K4).desc
    simp
    let f := s.π.app .one
    apply f ≫ F.toKPresheafFunctorObjMap ?_



    sorry





namespace TopCat.Sheaf

open TopCat.Presheaf

--variable (F : Sheaf A (of X))

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

      let J := WalkingCospan
      let K := (K1.openNhds × K4.openNhds)ᵒᵖ
      let Diag : J ⥤ K ⥤ A := sorry

      #check IsLimitConeOfColimF (J := WalkingCospan) (K := (K1.openNhds × K4.openNhds)ᵒᵖ) (F := by


        sorry)


      sorry
    · constructor
      sorry
  · sorry

#min_imports
