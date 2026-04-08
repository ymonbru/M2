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
def DiagO : WalkingCospan ⥤ (K1.openNhds × K2.openNhds)ᵒᵖ ⥤ (Opens X)ᵒᵖ := cospan (X := (forgetRight K1 K2).op) (Y := (forgetLeft K1 K2).op) (Z := (inter K1 K2).op) (NatTrans.op ⟨fun U => homOfLE (inf_le_right ),by aesop_cat⟩) (NatTrans.op ⟨fun U => homOfLE (inf_le_left),by aesop_cat⟩)

/-def DiagO : (K1.openNhds × K2.openNhds)ᵒᵖ ⥤ WalkingCospan ⥤ (Opens X)ᵒᵖ  where
  obj U := cospan (op (homOfLE inf_le_left): op U.unop.1.val ⟶ op (U.unop.1.val ⊓ U.unop.2.val) ) (op (homOfLE inf_le_right ): op U.unop.2.val ⟶ op (U.unop.1.val ⊓ U.unop.2.val))
  map {U V} i := by
    apply cospanHomMk _ (op i.unop.1) (op i.unop.2)
    apply op
    apply homOfLE
    exact inf_le_inf (leOfHom i.unop.1) (leOfHom i.unop.2)-/

@[simps!]
def Diag : WalkingCospan ⥤ (K1.openNhds × K2.openNhds)ᵒᵖ  ⥤ A :=
  let W := (Functor.whiskeringRight (K1.openNhds × K2.openNhds)ᵒᵖ _ _).obj F;
  ((Functor.whiskeringRight WalkingCospan _ _).obj W).obj (DiagO K1 K2)

def LjD : Cone (Diag F K2 K3) where
  pt := (union K2 K3).op ⋙ F
  π:= by
    refine cospanHomMk ?_ ?_ ?_ ?_ ?_
    · apply Functor.whiskerRight
      exact NatTrans.op ⟨fun U => homOfLE (inf_le_sup),by aesop_cat⟩
    · apply Functor.whiskerRight
      exact NatTrans.op ⟨fun U => homOfLE (le_sup_right),by aesop_cat⟩
    · apply Functor.whiskerRight
      exact NatTrans.op ⟨fun U => homOfLE (le_sup_left),by aesop_cat⟩
    · ext
      simp
      rw [← F.map_comp]
      rfl
    · ext
      simp
      rw [← F.map_comp]
      rfl

set_option backward.isDefEq.respectTransparency false in
def CategoryTheory.Limits.Cone.eval {J K C : Type*} [Category J] [Category K] [Category C] { F : J ⥤ K ⥤ C } (c : Cone F) (U : K ) : (Cone (F.flip.obj U)) where
  pt := c.pt.obj U
  π.app j := (c.π.app j).app U
  π.naturality {j k} f:= by
    dsimp
    rw [← NatTrans.comp_app, c.π.naturality' f]
    simp



def hLjD (F : Sheaf A (of X)): IsLimit (LjD F.obj K2 K3) where
  lift s := ⟨fun U => by

      let c : PullbackCone (F.obj.map (homOfLE (inf_le_left (a := U.unop.1.val) (b := U.unop.2.val))).op) (F.obj.map (homOfLE inf_le_right).op) := by
        unfold PullbackCone
        let c := s.eval U
        unfold Diag DiagO at c
        simp at c
        exact c
      let c:= s.eval U

      exact (Sheaf.isLimitPullbackCone F U.unop.1.val U.unop.2.val).lift c,sorry⟩
    --sorry

def LkD : Cocone (Diag F K2 K3).flip where
  pt := cospan (F.toKPresheafFunctorObjMap (homOfLE h.le₁₃)) (F.toKPresheafFunctorObjMap (homOfLE h.le₁₂))
  ι.app U := by
    refine cospanHomMk ?_ ?_ ?_ ?_ ?_
    · exact  F.ιToKPresheafFunctorObjObj ⟨_,by
      apply Set.subset_inter
      exact Set.Subset.trans h.le₁₂ U.unop.1.property
      exact Set.Subset.trans h.le₁₃ U.unop.2.property⟩
    · exact  F.ιToKPresheafFunctorObjObj ⟨_, U.unop.2.property⟩
    · exact  F.ιToKPresheafFunctorObjObj ⟨_, U.unop.1.property⟩

    · simp [Diag, DiagO, ]
      unfold TopCat.Presheaf.ιToKPresheafFunctorObjObj
      forceColimW

      apply op
      apply homOfLE
      simp [baseChangeOpenNhds]
      exact Subtype.mk_le_mk.mpr inf_le_right

    · simp [Diag, DiagO, ]
      unfold TopCat.Presheaf.ιToKPresheafFunctorObjObj
      forceColimW

      apply op
      apply homOfLE
      simp [baseChangeOpenNhds]
      exact Subtype.mk_le_mk.mpr inf_le_left
  ι.naturality {U V} i := by
    simp [Diag, DiagO]
    ext x
    match x with
      | .one =>
        simp [TopCat.Presheaf.ιToKPresheafFunctorObjObj]
        forceColimW
        apply op
        apply homOfLE
        exact Subtype.mk_le_mk.mpr (inf_le_inf (leOfHom i.unop.1) (leOfHom i.unop.2) )
      | .left =>
        simp [TopCat.Presheaf.ιToKPresheafFunctorObjObj]
        forceColimW
        apply op
        apply homOfLE
        exact Subtype.mk_le_mk.mpr (leOfHom i.unop.2)
      | .right =>
        simp [TopCat.Presheaf.ιToKPresheafFunctorObjObj]
        forceColimW
        apply op
        apply homOfLE
        exact Subtype.mk_le_mk.mpr (leOfHom i.unop.1)

def hLkD : IsColimit (LkD F K1 K2 K3 K4 h) where
  desc := sorry

def LkLjD : Cocone (LjD F K1 K2).pt := colimit.cocone _

def hLkLjD : IsColimit (LkLjD F K1 K2 ) := colimit.isColimit (LjD F K1 K2).pt

def LjLkD : Cone (LkD F K1 K2 K3 K4 h).pt where
  pt := F.toKPresheafFunctorObjObj K4
  π.app x := match x with
    |.one => F.toKPresheafFunctorObjMap (homOfLE <| h.le₁₂.trans h.le₂₄)
    |.left =>  F.toKPresheafFunctorObjMap (homOfLE <| h.le₃₄)
    |.right =>  F.toKPresheafFunctorObjMap (homOfLE <| h.le₂₄)
  π.naturality := by sorry

def hLjLkD : IsLimit (LjLkD F K1 K2 K3 K4 h) where
  lift := by sorry





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
