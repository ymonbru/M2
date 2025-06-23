import M2.alpha
import M2.colimOfColimEqColim
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.OpensLeCover
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.Topology.Sheaves.Stalks
--import Mathlib.CategoryTheory.Limits.Fubini
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite TopCat TopCat.Presheaf
open ZeroObject

universe u v w z

variable (X : Type w) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
variable (C : Type u) [Category.{v, u} C] [HasLimitsOfSize.{w,w} C] [HasColimitsOfSize.{w,w} C]

variable (G : Ksheaf X C) (F : Sheaf C (of X))

noncomputable section

#check TopCat.Presheaf.IsSheaf ((AlphaDownStar).obj (G.carrier):Presheaf C (of X))

@[simp]
theorem KshToSh: TopCat.Presheaf.IsSheaf  ((AlphaDownStar).obj (G.carrier) : Presheaf C (of X)):= by
  --probablement mieux d'utiliser isSheaf_iff_isSheafPairwiseIntersections
  apply (isSheaf_iff_isSheafPairwiseIntersections _).2
  unfold IsSheafPairwiseIntersections
  intro i U
  apply Nonempty.intro
  constructor
  · intro s j
    sorry
  · sorry
  · sorry


@[simps]
def shAlphaDownStarF : Sheaf C (of X) where
  val:= (AlphaDownStar).obj (G.carrier)
  cond := (KshToSh X C G)

@[simps]
def shAlphaDownStar : (Ksheaf X C) ⥤ Sheaf C (of X) where
  obj _ := shAlphaDownStarF X C _
  map f := Sheaf.Hom.mk ((AlphaDownStar).map f)
  map_id _ := by
    apply Sheaf.Hom.ext
    apply (AlphaDownStar).map_id
  map_comp _ _:= by
    apply Sheaf.Hom.ext
    apply (AlphaDownStar).map_comp

@[simps!]
def TerminalOpBotsubU : IsTerminal (op ⟨⊥ , by simp⟩ : (KsubU_cat (⊥ : Compacts X) trueCond)ᵒᵖ ) := by
  apply terminalOpOfInitial
  apply IsInitial.ofUniqueHom
  · intro _ _
    apply eq_of_comp_right_eq
    intro _ _
    rfl
  · intro
    apply homOfLE
    intro x hx
    rcases hx


variable (K1 K2 : Compacts X)

def presheafFunctor : (Opens X)ᵒᵖ ⥤ C := by exact ((Sheaf.forget C (of X)).obj F)
variable (K : Compacts X)

/--An helper to buil natural transformation between functors WalkingCospan ⥤ C. In particular it makes obvious for simp the naturality case for id, wich simp cant close in some particular cases-/
@[simps]
def natTransWcspFunc {C : Type u} [Category.{v} C] (F G : WalkingCospan ⥤ C) (fL: F.obj .left ⟶ G.obj .left)(fR: F.obj .right ⟶ G.obj .right) (fO: F.obj .one ⟶ G.obj .one) (hOL : F.map WalkingCospan.Hom.inl ≫ fO = fL ≫ G.map WalkingCospan.Hom.inl) (hOR : F.map WalkingCospan.Hom.inr ≫ fO = fR ≫ G.map WalkingCospan.Hom.inr) : F ⟶ G where
  app x:= match x with
    |.left => fL
    |.right => fR
    |.one => fO
  naturality x y f := match f with
    | WalkingCospan.Hom.inl => hOL
    | WalkingCospan.Hom.inr => hOR
    | WalkingCospan.Hom.id _ => by simp

/-- The specialisation of natTransWcspFunc in the case where the functors are obtain by cospan-/
@[simps!]
def natTransCospan {C : Type u} [Category.{v} C] { A1 B1 C1 A2 B2 C2 : C} { f1 : A1 ⟶ B1} { g1 : C1 ⟶ B1} { f2 : A2 ⟶ B2} { g2 : C2 ⟶ B2} (a : A1 ⟶ A2) (b : B1 ⟶ B2) (c : C1 ⟶ C2) (hab : f1 ≫ b = a ≫ f2) (hbc : g1 ≫ b = c ≫ g2):  cospan f1 g1 ⟶ cospan f2 g2 :=  natTransWcspFunc (cospan f1 g1) _ a c b hab hbc

/-- For any pair U1 U2 (containing K1 and K2) the diagram U1 → U1 ∩ U2 ← U2 in a functorial way-/
@[simps]
def truc9 : ((KsubU_cat K1 trueCond) × (KsubU_cat K2 trueCond) )ᵒᵖ  ⥤ WalkingCospan ⥤ (Opens X)ᵒᵖ where
  obj U := cospan (op (homOfLE inf_le_left): op U.unop.1.obj ⟶ op (U.unop.1.obj ⊓ U.unop.2.obj) ) (op (homOfLE inf_le_right ): op U.unop.2.obj ⟶ op (U.unop.1.obj ⊓ U.unop.2.obj))
  map {U V} f := natTransCospan (op f.unop.1) (op (subK1SubK2toSubK1InterK2.map f.unop)) (op f.unop.2) (rfl) (rfl)

@[simps!]
def jLeft : ((KsubU_cat K1 trueCond) × (KsubU_cat K2 trueCond) )ᵒᵖ ⥤ (Opens X)ᵒᵖ := (truc9 X K1 K2).flip.obj .left

@[simps!]
def jRight : ((KsubU_cat K1 trueCond) × (KsubU_cat K2 trueCond) )ᵒᵖ ⥤ (Opens X)ᵒᵖ := (truc9 X K1 K2).flip.obj .right

@[simps!]
def jOne : ((KsubU_cat K1 trueCond) × (KsubU_cat K2 trueCond) )ᵒᵖ ⥤ (Opens X)ᵒᵖ := (truc9 X K1 K2).flip.obj .one

def jLToJO : (jLeft X K1 K2) ⟶ (jOne X K1 K2) where
  app U := op (homOfLE (by simp))

def jRToJO : (jRight X K1 K2) ⟶ (jOne X K1 K2) where
  app U := op (homOfLE (by simp))

#check colimMap ( whiskerRight (jLToJO X K1 K2) (presheafFunctor _ _ F))

/-- Whiskering truc9 by F: For any pair U1 U2 (containing K1 and K2) the diagram F(U1) → F(U1 ∩ U2) ← U2 in a functorial way-/
@[simps!]
def truc : ((KsubU_cat K1 trueCond) × (KsubU_cat K2 trueCond)) ᵒᵖ ⥤ (WalkingCospan ⥤ C) := let WToOInWToC := (whiskeringRight WalkingCospan _ _ ).obj (presheafFunctor _ _ F); ((whiskeringRight (KsubU_cat K1 trueCond × KsubU_cat K2 trueCond)ᵒᵖ _ _).obj  WToOInWToC).obj (truc9 X K1 K2)

/-- The diaram colimit_{K1 ⊆ U}F(U) → colimit_{K1 ∩ K2 ⊆ U}F(U) ← colimit_{K2 ⊆ U} F(U)-/
@[simps!]
def truc4Pt : WalkingCospan ⥤ C := by
  apply cospan
  exact colimMap ( whiskerRight (jLToJO X K1 K2) (presheafFunctor _ _ F))
  exact colimMap ( whiskerRight (jRToJO X K1 K2) (presheafFunctor _ _ F))
  /-exact colimit.pre (Functor.op  (ObjectProperty.ι _ ) ⋙ presheafFunctor X C F) (Functor.op ( K1subK2subU trueCond (homOfLE (inf_le_left) : K1 ⊓ K2 ⟶ K1)))
  exact colimit.pre (Functor.op  (ObjectProperty.ι _ ) ⋙ presheafFunctor X C F) (Functor.op ( K1subK2subU trueCond (homOfLE (inf_le_right) : K1 ⊓ K2 ⟶ K2)))-/
set_option maxHeartbeats 2005000 in

/-- the natural transformation that makes truc4Pt a Cocone over truc-/
@[simps]
def truc4ι : truc X C F K1 K2 ⟶ (Functor.const (KsubU_cat K1 trueCond × KsubU_cat K2 trueCond)ᵒᵖ).obj (truc4Pt X C F K1 K2) where
  app U := by
    apply (cospanCompIso _ _ _).hom ≫ _
    refine natTransCospan ?_ ?_ ?_ ?_ ?_
    · exact colimit.ι (jLeft X K1 K2 ⋙ presheafFunctor X C F) U
    · exact colimit.ι (jOne X K1 K2 ⋙ presheafFunctor X C F) U
    · exact colimit.ι (jRight X K1 K2 ⋙ presheafFunctor X C F) U
    · suffices (presheafFunctor X C F).map (op (homOfLE _)) ≫ colimit.ι (jOne X K1 K2 ⋙ presheafFunctor X C F) U = (presheafFunctor X C F).map ((jLToJO X K1 K2).app U) ≫ colimit.ι (jOne X K1 K2 ⋙ presheafFunctor X C F) U by simpa
      rfl
    · suffices (presheafFunctor X C F).map (op (homOfLE _)) ≫ colimit.ι (jOne X K1 K2 ⋙ presheafFunctor X C F) U = (presheafFunctor X C F).map ((jRToJO X K1 K2).app U) ≫ colimit.ι (jOne X K1 K2 ⋙ presheafFunctor X C F) U by simpa
      rfl



    /-· exact colimit.ι ((K1subK2subU trueCond (homOfLE inf_le_left)).op ⋙ (ObjectProperty.ι (KsubU (K1 ⊓ K2) trueCond)).op ⋙ presheafFunctor X C F) (op U.unop.1)
    · exact colimit.ι ((ObjectProperty.ι (KsubU (K1 ⊓ K2) trueCond)).op ⋙ presheafFunctor X C F) ( op (subK1SubK2toSubK1InterK2.obj U.unop))
    · exact colimit.ι ((K1subK2subU trueCond (homOfLE inf_le_right)).op ⋙ (ObjectProperty.ι (KsubU (K1 ⊓ K2) trueCond)).op ⋙ presheafFunctor X C F) (op U.unop.2)

    · suffices (presheafFunctor X C F).map (op (homOfLE _)) ≫ colimit.ι ((ObjectProperty.ι (KsubU (K1 ⊓ K2) trueCond)).op ⋙ presheafFunctor X C F) (op { obj := (unop U).1.obj ⊓ (unop U).2.obj, property := _ }) = colimit.ι ((ObjectProperty.ι (KsubU (K1 ⊓ K2) trueCond)).op ⋙ presheafFunctor X C F) (op ((K1subK2subU trueCond (homOfLE _)).obj (unop U).1)) by simpa

      apply Eq.symm
      rw [ ← colimit.w _ ?_]
      apply eq_whisker
      repeat rfl
      apply op
      apply homOfLE
      simp
    · suffices (presheafFunctor X C F).map (op (homOfLE _)) ≫ colimit.ι ((ObjectProperty.ι (KsubU (K1 ⊓ K2) trueCond)).op ⋙ presheafFunctor X C F) (op { obj := (unop U).1.obj ⊓ (unop U).2.obj, property := _ }) = colimit.ι ((ObjectProperty.ι (KsubU (K1 ⊓ K2) trueCond)).op ⋙ presheafFunctor X C F) (op ((K1subK2subU trueCond (homOfLE _)).obj (unop U).2)) by simpa

      apply Eq.symm
      rw [ ← colimit.w _ ?_]
      apply eq_whisker
      repeat rfl
      apply op
      apply homOfLE
      simp-/
  naturality U V f:= by
    ext x
    match x with
      | .left =>
        suffices (presheafFunctor X C F).map (op f.unop.1) ≫ colimit.ι (jLeft X K1 K2 ⋙ presheafFunctor X C F) V = colimit.ι (jLeft X K1 K2 ⋙ presheafFunctor X C F) U by simpa
        rw [← colimit.w _ f]
        rfl
      | .right =>
        suffices (presheafFunctor X C F).map (op f.unop.2) ≫ colimit.ι (jRight X K1 K2 ⋙ presheafFunctor X C F) V = colimit.ι (jRight X K1 K2 ⋙ presheafFunctor X C F) U by simpa
        rw [← colimit.w _ f]
        rfl
      | .one =>
        simp
        rw [← colimit.w _ f]
        rfl
    /-ext x
    match x with
      | .left =>
        suffices (presheafFunctor X C F).map (op f.unop.1) ≫ colimit.ι ((K1subK2subU trueCond (homOfLE _ )).op ⋙ (ObjectProperty.ι (KsubU (K1 ⊓ K2) trueCond)).op ⋙ presheafFunctor X C F) (op (unop V).1) = colimit.ι ((K1subK2subU trueCond (homOfLE _ )).op ⋙ (ObjectProperty.ι (KsubU (K1 ⊓ K2) trueCond)).op ⋙ presheafFunctor X C F) (op (unop U).1) by simpa

        have : (op (unop U).1) ⟶ (op (unop V).1) := op f.unop.1
        rw [← colimit.w _ this]
        rfl
      | .right =>
        suffices (presheafFunctor X C F).map (op f.unop.2) ≫ colimit.ι ((K1subK2subU trueCond (homOfLE _ )).op ⋙ (ObjectProperty.ι (KsubU (K1 ⊓ K2) trueCond)).op ⋙ presheafFunctor X C F) (op (unop V).2) = colimit.ι ((K1subK2subU trueCond (homOfLE _ )).op ⋙ (ObjectProperty.ι (KsubU (K1 ⊓ K2) trueCond)).op ⋙ presheafFunctor X C F) (op (unop U).2) by simpa

        have : (op (unop U).2) ⟶ (op (unop V).2) := op f.unop.2
        rw [← colimit.w _ this]
        rfl
      | .one =>
        suffices (presheafFunctor X C F).map (op (homOfLE _)) ≫ colimit.ι ((ObjectProperty.ι (KsubU (K1 ⊓ K2) trueCond)).op ⋙ presheafFunctor X C F) (op (subK1SubK2toSubK1InterK2.obj (unop V))) = colimit.ι ((ObjectProperty.ι (KsubU (K1 ⊓ K2) trueCond)).op ⋙ presheafFunctor X C F) (op (subK1SubK2toSubK1InterK2.obj (unop U))) by simpa

        have : (op (subK1SubK2toSubK1InterK2.obj (unop U))) ⟶ (op (subK1SubK2toSubK1InterK2.obj (unop V))) := op (subK1SubK2toSubK1InterK2.map f.unop)
        rw [ ← colimit.w _ this ] -- ici ça veux du heart beat
        rfl-/

/-- The cocne structre of tuc4Pt over truc-/
@[simps]
def truc4 : Cocone (truc X C F K1 K2 ) where
  pt := truc4Pt X C F K1 K2
  ι := truc4ι X C F K1 K2

variable (s : Cocone (truc X C F K1 K2)) (x : WalkingCospan)

/-instance : Top (KsubU_cat K1 trueCond) where
  top := by
    use ⊤
    simp-/

@[simps]
def truc4DescCoconeXι (j : ((KsubU_cat K1 trueCond) × (KsubU_cat K2 trueCond) )ᵒᵖ ⥤ (Opens X)ᵒᵖ ) (h : ∀ U, unop (((truc9 X K1 K2).obj U).obj x) ≤ unop (j.obj U)
 ): j ⋙ presheafFunctor X C F ⟶ (Functor.const _).obj (s.pt.obj x) where
  app U := (presheafFunctor X C F).map ( op (homOfLE (h U))) ≫ (s.ι.app  U).app x
  naturality U V f:= by
    suffices (presheafFunctor X C F).map (j.map f) ≫ (presheafFunctor X C F).map (op (homOfLE _)) ≫ (s.ι.app V).app x = (presheafFunctor X C F).map (op (homOfLE _)) ≫ (s.ι.app U).app x by simpa

    have : (truc X C F K1 K2).map f ≫ s.ι.app V = s.ι.app U := by
      rw [ s.ι.naturality f]
      simp
    rw [← this, ← Category.assoc, ← (presheafFunctor X C F).map_comp]

    suffices _ ≫ _ = _ ≫_ ≫ _ by dsimp; assumption
    rw [← Category.assoc, ← (presheafFunctor X C F).map_comp]
    rfl
/-
@[simps]
def truc4DescCoconeLeftι : (K1subK2subU trueCond (homOfLE inf_le_left)).op ⋙ (ObjectProperty.ι (KsubU (K1 ⊓ K2) trueCond)).op ⋙ presheafFunctor X C F ⟶ (Functor.const (KsubU_cat K1 trueCond)ᵒᵖ).obj (s.pt.obj .left) where
  app U := (s.ι.app  (op ⟨U.unop, ⊤⟩)).app .left
  naturality U V f:= by
    suffices (presheafFunctor X C F).map (homOfLE _).op ≫ (s.ι.app (op (unop V, ⊤))).app .left = (s.ι.app (op (unop U, ⊤))).app .left by simpa

    have : ((truc X C F K1 K2).obj (op (unop U, ⊤))).map (WalkingCospan.Hom.id .left) ≫ (s.ι.app (op (unop U, ⊤))).app .left = (s.ι.app (op (unop U, ⊤))).app .left := by
      rw [(s.ι.app (op (unop U, ⊤))).naturality (WalkingCospan.Hom.id .left)]
      simp
    rw [← this]

    have : (truc X C F K1 K2).map (op (f.unop, 𝟙 ⊤)) ≫ s.ι.app (op (unop V, ⊤)) = s.ι.app (op (unop U, ⊤)) := by
      rw [s.ι.naturality ((op ⟨f.unop, 𝟙 _⟩) : (op ⟨U.unop, ⊤⟩) ⟶ (op ⟨V.unop, ⊤⟩))]
      simp
    rw [← this]
    suffices (presheafFunctor X C F).map (homOfLE (leOfHom f.unop)).op ≫ (s.ι.app (op (unop V, ⊤))).app .left = (presheafFunctor X C F).map (op f.unop) ≫ (s.ι.app (op (unop V, ⊤))).app .left by simpa [truc]

    rfl
/- quasiment la même preuve que pour left : essayer d'en extraire un truc plus général en fonction du cas de .one-/
@[simps]
def truc4DescCoconeRightι : (K1subK2subU trueCond (homOfLE inf_le_right)).op ⋙ (ObjectProperty.ι (KsubU (K1 ⊓ K2) trueCond)).op ⋙ presheafFunctor X C F ⟶ (Functor.const (KsubU_cat K2 trueCond)ᵒᵖ).obj (s.pt.obj .right) where
  app U := (s.ι.app  (op ⟨ ⊤, U.unop⟩)).app .right
  naturality U V f:= by
    suffices (presheafFunctor X C F).map (homOfLE _).op ≫ (s.ι.app (op (⊤, unop V))).app .right = (s.ι.app (op (⊤, unop U))).app .right by simpa
    have : ((truc X C F K1 K2).obj (op (⊤, unop U))).map (WalkingCospan.Hom.id .right) ≫ (s.ι.app (op (⊤, unop U))).app .right = (s.ι.app (op (⊤, unop U))).app .right := by
      rw [(s.ι.app (op (⊤, unop U))).naturality (WalkingCospan.Hom.id .right)]
      simp
    rw [← this]

    have : (truc X C F K1 K2).map (op (𝟙 ⊤, f.unop)) ≫ s.ι.app (op (⊤, unop V)) = s.ι.app (op (⊤, unop U)) := by
      rw [s.ι.naturality ((op ⟨𝟙 _, f.unop⟩) : (op ⟨⊤, U.unop⟩) ⟶ (op ⟨⊤, V.unop⟩))]
      simp
    rw [← this]
    suffices (presheafFunctor X C F).map (homOfLE (leOfHom f.unop)).op ≫ (s.ι.app (op (⊤, unop V))).app .right = (presheafFunctor X C F).map (op f.unop) ≫ (s.ι.app (op (⊤, unop V))).app .right by simpa [truc]
    rfl


def liftUAsInter (U : (KsubU_cat (K1 ⊓ K2) trueCond)) : (KsubU_cat K1 trueCond × KsubU_cat K2 trueCond) := by sorry

def liftUAsInterSpec1 (U : KsubU_cat K1 trueCond × KsubU_cat K2 trueCond):  (liftUAsInter X K1 K2 (subK1SubK2toSubK1InterK2.obj U)) ⟶ U:= by sorry

lemma liftUAsInterSpec2 (U : (KsubU_cat (K1 ⊓ K2) trueCond)):  (liftUAsInter _ _ _ U).1.obj ⊓ (liftUAsInter _ _ _ U).2.obj ≤ U.obj := by sorry



@[simps]
def truc4DescCoconeOneι : (ObjectProperty.ι (KsubU (K1 ⊓ K2) trueCond)).op ⋙ presheafFunctor X C F ⟶ (Functor.const (ObjectProperty.FullSubcategory (KsubU (K1 ⊓ K2) trueCond))ᵒᵖ).obj (s.pt.obj WalkingCospan.one) where
  app U := by
    simp
    /-let Vk : {K1 K2 : Compacts X} → (K : Compacts X) → (U : KsubU_cat (K1 ⊓ K2) trueCond) → Opens X := fun K => fun U => ⟨U.obj.carrier ∪ K.carrierᶜ, IsOpen.union (U.obj.is_open') ( isOpen_compl_iff.mpr (IsCompact.isClosed (K.isCompact')))⟩

    let K1subVK2 : {K1 K2 : Compacts X} → (K L : Compacts X) → (U : KsubU_cat (K1 ⊓ K2) trueCond) → (h : (K ⊓ L).carrier ⊆ U.obj.carrier ) → KsubU_cat K trueCond := fun K => fun L => fun U => fun h => by
      use (Vk L U)
      constructor
      · intro x h1x
        by_cases h2x : x ∈ L
        · left
          apply h
          exact ⟨h1x, h2x⟩
        · right
          assumption
      · rfl

    let V : (KsubU_cat K1 trueCond × KsubU_cat K2 trueCond)ᵒᵖ := by
      apply op
      constructor
      · exact K1subVK2 K1 K2 U.unop U.unop.property.1
      · apply K1subVK2 K2 K1 U.unop
        rintro x ⟨h2x, h1x⟩
        apply U.unop.property.1 ⟨ h1x, h2x⟩-/

    apply _ ≫ (s.ι.app (op (liftUAsInter _ _ _ U.unop))).app .one

    apply (presheafFunctor X C F).map
    apply op
    apply homOfLE
    exact liftUAsInterSpec2 X K1 K2 U.unop
    /-unfold V K1subVK2 Vk
    --simp
    rintro x ⟨ h1x, h2x⟩
    cases h1x
    · assumption
    · cases h2x
      · assumption
      · sorry-/

  naturality U V f:= by
    simp
    rw [← Category.assoc]
    apply eq_whisker
    rw [← (presheafFunctor X C F).map_comp]
    rfl

@[simps]
def truc4DescCoconeLeft : Cocone ((K1subK2subU trueCond (homOfLE inf_le_left)).op ⋙ (ObjectProperty.ι (KsubU (K1 ⊓ K2) trueCond)).op ⋙ presheafFunctor X C F) where
  pt := s.pt.obj .left
  ι := truc4DescCoconeLeftι X C F K1 K2 s

@[simps]
def truc4DescCoconeRight : Cocone ((K1subK2subU trueCond (homOfLE inf_le_right)).op ⋙ (ObjectProperty.ι (KsubU (K1 ⊓ K2) trueCond)).op ⋙ presheafFunctor X C F) where
  pt := s.pt.obj .right
  ι := truc4DescCoconeRightι X C F K1 K2 s

@[simps]
def truc4DescCoconeOne : Cocone ((ObjectProperty.ι (KsubU (K1 ⊓ K2) trueCond)).op ⋙ presheafFunctor X C F) where
  pt := s.pt.obj .one
  ι := truc4DescCoconeOneι X C F K1 K2 s
-- (K1subK2subU trueCond (homOfLE inf_le_left)).op ⋙ (ObjectProperty.ι (KsubU (K1 ⊓ K2) trueCond)).op ⋙ presheafFunctor X C F ⟶ (Functor.const (KsubU_cat K1 trueCond)ᵒᵖ).obj (s.pt.obj .left)-/

@[simps]
def truc4DescCoconeX (j : ((KsubU_cat K1 trueCond) × (KsubU_cat K2 trueCond) )ᵒᵖ ⥤ (Opens X)ᵒᵖ ) (h : ∀ U, unop (((truc9 X K1 K2).obj U).obj x) ≤ unop (j.obj U)
 ): Cocone (j ⋙ presheafFunctor X C F) where
  pt := s.pt.obj x
  ι := truc4DescCoconeXι X C F K1 K2 s x j h

@[simps!]
def truc4Desc : truc4Pt X C F K1 K2 ⟶ s.pt := by
  refine natTransWcspFunc _ _ ?_ ?_ ?_ ?_ ?_

  --· exact colimit.desc _ (truc4DescCoconeLeft _ _ _ _ _ _)
  --· exact colimit.desc _ (truc4DescCoconeRight _ _ _ _ _ _)
  --· exact colimit.desc _ (truc4DescCoconeOne _ _ _ _ _ _)
  · exact colimit.desc _ (truc4DescCoconeX _ _ F _ _ s .left (jLeft X K1 K2)  (fun _ => by simp))



  · exact colimit.desc _ (truc4DescCoconeX _ _ F _ _ s .right (jRight X K1 K2)  (by simp))

  · exact colimit.desc _ (truc4DescCoconeX _ _ _ _ _ _ .one (jOne X K1 K2)  (by simp))

  · apply colimit.hom_ext
    intro U
    suffices (presheafFunctor X C F).map ((jLToJO X K1 K2).app U) ≫
    (presheafFunctor X C F).map (op (𝟙 ((unop U).1.obj ⊓ (unop U).2.obj))) ≫ (s.ι.app U).app WalkingCospan.one = (presheafFunctor X C F).map (op (𝟙 (unop U).1.obj)) ≫ (s.ι.app U).app WalkingCospan.left ≫ s.pt.map WalkingCospan.Hom.inl by simpa

    have : (presheafFunctor X C F).map (op (homOfLE (truc9._proof_8 X K1 K2 U))) ≫ (s.ι.app U).app WalkingCospan.one = (s.ι.app U).app WalkingCospan.left ≫ s.pt.map WalkingCospan.Hom.inl := by
      exact (s.ι.app U).naturality WalkingCospan.Hom.inl
    rw [← this]

    suffices _ ≫ _ ≫ _ = _ ≫_ ≫ _ by dsimp; assumption
    rw [← Category.assoc, ← (presheafFunctor X C F).map_comp, ← Category.assoc, ← (presheafFunctor X C F).map_comp]
    rfl
  · apply colimit.hom_ext
    intro U
    suffices (presheafFunctor X C F).map ((jRToJO X K1 K2).app U) ≫
    (presheafFunctor X C F).map (op (𝟙 ((unop U).1.obj ⊓ (unop U).2.obj))) ≫ (s.ι.app U).app WalkingCospan.one = (presheafFunctor X C F).map (op (𝟙 (unop U).2.obj)) ≫
    (s.ι.app U).app WalkingCospan.right ≫ s.pt.map WalkingCospan.Hom.inr by simpa

    have : (presheafFunctor X C F).map (op (homOfLE (truc9._proof_9 X K1 K2 U))) ≫ (s.ι.app U).app WalkingCospan.one = (s.ι.app U).app WalkingCospan.right ≫ s.pt.map WalkingCospan.Hom.inr := by
      exact (s.ι.app U).naturality WalkingCospan.Hom.inr
    rw [← this]

    suffices _ ≫ _ ≫ _ = _ ≫_ ≫ _ by dsimp; assumption
    rw [← Category.assoc, ← (presheafFunctor X C F).map_comp, ← Category.assoc, ← (presheafFunctor X C F).map_comp]
    rfl


   /-
  · apply colimit.hom_ext
    intro U
    suffices (presheafFunctor X C F).map (op (homOfLE _)) ≫ (s.ι.app (op (liftUAsInter X K1 K2 ((K1subK2subU trueCond (homOfLE _)).obj (unop U))))).app .one = (s.ι.app (op (unop U, ⊤))).app .left ≫ s.pt.map WalkingCospan.Hom.inl by simpa

    have : ((truc X C F K1 K2).obj (op (unop U, ⊤))).map WalkingCospan.Hom.inl ≫ (s.ι.app (op (unop U, ⊤))).app .one = (s.ι.app (op (unop U, ⊤))).app .left ≫ s.pt.map WalkingCospan.Hom.inl := by exact (s.ι.app (op (unop U, ⊤))).naturality WalkingCospan.Hom.inl

    rw [← this]
    have f : (op (unop U, ⊤)) ⟶  op (liftUAsInter X K1 K2 ((K1subK2subU trueCond (homOfLE (truc4Pt._proof_18 X K1 K2))).obj (unop U))) := by
      apply op
      constructor
      · simp
        #check (liftUAsInterSpec2 X K1 K2 ((K1subK2subU trueCond (homOfLE _)).obj (unop U)))
        -- il faut faire en sorte que si U recouvre K1 alors le relèvement de U (en tant que K1 ∩ K2 ⊆ U ) soit inclus dans K1
        sorry
      · simp
        apply homOfLE
        intro _ _
        trivial

    have : (truc X C F K1 K2).map f ≫ s.ι.app (op (liftUAsInter X K1 K2 ((K1subK2subU trueCond (homOfLE _)).obj (unop U)))) = s.ι.app (op (unop U, ⊤)) := by
      rw [ s.ι.naturality f]
      simp

    rw [← this]
    suffices _ ≫ _ = _ ≫ _ ≫ _ by dsimp; assumption
    rw [← Category.assoc, ← (presheafFunctor X C F).map_comp]
    rfl
  · apply colimit.hom_ext
    intro U
    suffices (presheafFunctor X C F).map (op (homOfLE _)) ≫ (s.ι.app (op (liftUAsInter X K1 K2 ((K1subK2subU trueCond (homOfLE _)).obj (unop U))))).app .one = (s.ι.app (op (⊤, unop U))).app .right ≫ s.pt.map WalkingCospan.Hom.inr by simpa

    have : ((truc X C F K1 K2).obj (op (⊤, unop U))).map WalkingCospan.Hom.inr ≫ (s.ι.app (op (⊤, unop U))).app .one = (s.ι.app (op (⊤, unop U))).app .right ≫ s.pt.map WalkingCospan.Hom.inr := by exact (s.ι.app (op (⊤, unop U))).naturality WalkingCospan.Hom.inr

    rw [← this]
    have f : (op (⊤, unop U)) ⟶ op (liftUAsInter X K1 K2 ((K1subK2subU trueCond (homOfLE (truc4Pt._proof_20 X K1 K2))).obj (unop U))) := by
      apply op
      constructor
      · simp
        apply homOfLE
        intro _ _
        trivial

      · simp
        #check (liftUAsInterSpec2 X K1 K2 ((K1subK2subU trueCond (homOfLE _)).obj (unop U)))
        -- il faut faire en sorte que si U recouvre K2 alors le relèvement de U (en tant que K1 ∩ K2 ⊆ U ) soit inclus dans K2
        sorry

    have : (truc X C F K1 K2).map f ≫ s.ι.app (op (liftUAsInter X K1 K2 ((K1subK2subU trueCond (homOfLE _)).obj (unop U)))) = s.ι.app (op (⊤, unop U)) := by
      rw [ s.ι.naturality f]
      simp

    rw [← this]
    suffices _ ≫ _ = _ ≫ _ ≫ _ by dsimp; assumption
    rw [← Category.assoc, ← (presheafFunctor X C F).map_comp]
    rfl-/

def truc4Colim : IsColimit (truc4 X C F K1 K2) where
  desc s := truc4Desc X C F K1 K2 s
  fac s U := by
    ext x
    match x with
      | .left =>
        suffices (presheafFunctor X C F).map (op (𝟙 (unop U).1.obj)) ≫ (s.ι.app U).app WalkingCospan.left = (s.ι.app U).app WalkingCospan.left by simpa
        suffices op (𝟙 (unop U).1.obj) = 𝟙 ((op U.unop.1.obj))  by
          rw [this]
          simp
        rfl
      | .right =>
        suffices (presheafFunctor X C F).map (op (𝟙 (unop U).2.obj)) ≫ (s.ι.app U).app WalkingCospan.right = (s.ι.app U).app WalkingCospan.right by simpa
        suffices op (𝟙 (unop U).2.obj) = 𝟙 ((op U.unop.2.obj))  by
          rw [this]
          simp
        rfl
      | .one =>
        suffices  (presheafFunctor X C F).map (op (𝟙 ((unop U).1.obj ⊓ (unop U).2.obj))) ≫ (s.ι.app U).app WalkingCospan.one =
  (s.ι.app U).app WalkingCospan.one by simpa
        suffices op (𝟙 (((unop U).1.obj ⊓ (unop U).2.obj))) = 𝟙 ((op (((unop U).1.obj ⊓ (unop U).2.obj))))  by
          rw [this]
          simp
        rfl
    /-match x with
    |.left =>
      let f : (op ((unop U).1, ⊤)) ⟶ U := op ⟨ 𝟙 (unop U).1, homOfLE (fun _ _ => trivial)⟩

      suffices (s.ι.app (op ((unop U).1, ⊤))).app .left = (s.ι.app U).app .left by simpa

      have : (truc X C F K1 K2).map f ≫ s.ι.app U = s.ι.app (op ((unop U).1, ⊤)) := by
        rw [s.ι.naturality f]
        simp
      rw [← this]

      suffices (presheafFunctor X C F).map (op f.unop.1) ≫ (s.ι.app U).app .left = (s.ι.app U).app .left by
        rw [← this]
        dsimp
      have : op f.unop.1 = 𝟙 (op U.unop.1.obj) := by rfl
      rw [this]
      simp
    | .right =>
      let f : (op (⊤, (unop U).2)) ⟶ U := op ⟨homOfLE (fun _ _ => trivial), 𝟙 (unop U).2⟩

      suffices (s.ι.app (op (⊤, (unop U).2))).app .right = (s.ι.app U).app .right by simpa

      have : (truc X C F K1 K2).map f ≫ s.ι.app U = s.ι.app (op (⊤, (unop U).2)) := by
        rw [s.ι.naturality f]
        simp
      rw [← this]

      suffices (presheafFunctor X C F).map (op f.unop.2) ≫ (s.ι.app U).app .right = (s.ι.app U).app .right by
        rw [← this]
        dsimp
      have : op f.unop.2 = 𝟙 (op U.unop.2.obj) := by rfl
      rw [this]
      simp
    | .one =>
      suffices (presheafFunctor X C F).map (op (homOfLE _)) ≫ (s.ι.app (op (liftUAsInter X K1 K2 (subK1SubK2toSubK1InterK2.obj (unop U))))).app .one = (s.ι.app U).app WalkingCospan.one by simpa

      have f : U ⟶ op (liftUAsInter X K1 K2 (subK1SubK2toSubK1InterK2.obj (unop U))) :=  op (liftUAsInterSpec1 X K1 K2 (unop U))

      have : (truc X C F K1 K2).map f ≫ s.ι.app (op (liftUAsInter X K1 K2 (subK1SubK2toSubK1InterK2.obj (unop U)))) = s.ι.app U :=  by
        rw [ s.ι.naturality f]
        simp

      rw [← this]
      dsimp-/
  uniq s m hm := by
    ext x
    match x with
      | .left =>
        apply colimit.hom_ext
        intro U
        suffices colimit.ι (jLeft X K1 K2 ⋙ presheafFunctor X C F) U ≫ m.app WalkingCospan.left = (presheafFunctor X C F).map (op (𝟙 (unop U).1.obj)) ≫ (s.ι.app U).app WalkingCospan.left by simpa
        suffices op (𝟙 (unop U).1.obj) = 𝟙 ((op U.unop.1.obj))  by
          rw [this,  ← hm _]
          simp
        rfl
      | .right =>
        apply colimit.hom_ext
        intro U
        suffices colimit.ι (jRight X K1 K2 ⋙ presheafFunctor X C F) U ≫ m.app WalkingCospan.right = (presheafFunctor X C F).map (op (𝟙 (unop U).2.obj)) ≫ (s.ι.app U).app WalkingCospan.right by simpa
        suffices op (𝟙 (unop U).2.obj) = 𝟙 ((op U.unop.2.obj))  by
          rw [this,  ← hm _]
          simp
        rfl
      | .one =>
        apply colimit.hom_ext
        intro U
        suffices colimit.ι (jOne X K1 K2 ⋙ presheafFunctor X C F) U ≫ m.app WalkingCospan.one = (presheafFunctor X C F).map (op (𝟙 ((unop U).1.obj ⊓ (unop U).2.obj))) ≫ (s.ι.app U).app WalkingCospan.one by simpa
        suffices op (𝟙 (((unop U).1.obj ⊓ (unop U).2.obj))) = 𝟙 ((op (((unop U).1.obj ⊓ (unop U).2.obj))))  by
          rw [this, ← hm ]
          simp
        rfl
    /-
    match x with
      |.left =>
        apply colimit.hom_ext
        intro U
        suffices colimit.ι ((K1subK2subU trueCond (homOfLE _)).op ⋙ (ObjectProperty.ι (KsubU (K1 ⊓ K2) trueCond)).op ⋙ presheafFunctor X C F) U ≫ m.app .left = (s.ι.app (op (unop U, ⊤))).app .left by simpa
        rw [← hm _]
        simp
      |.right =>
        apply colimit.hom_ext
        intro U
        suffices colimit.ι ((K1subK2subU trueCond (homOfLE _)).op ⋙ (ObjectProperty.ι (KsubU (K1 ⊓ K2) trueCond)).op ⋙ presheafFunctor X C F) U ≫ m.app .right = (s.ι.app (op (⊤, unop U))).app .right by simpa
        rw [← hm _]
        simp

      |.one =>
        apply colimit.hom_ext
        intro U
        suffices colimit.ι ((ObjectProperty.ι (KsubU (K1 ⊓ K2) trueCond)).op ⋙ presheafFunctor X C F) U ≫ m.app WalkingCospan.one = (presheafFunctor X C F).map (op (homOfLE _)) ≫ (s.ι.app ( op (liftUAsInter X K1 K2 U.unop))).app WalkingCospan.one by simpa
        rw [← hm _]

        simp
        rw [← Category.assoc]
        apply eq_whisker
        have f: U ⟶ (op (subK1SubK2toSubK1InterK2.obj (liftUAsInter X K1 K2 (unop U)))) := by
          apply op
          apply homOfLE
          exact (liftUAsInterSpec2 X K1 K2 U.unop)
        rw [← colimit.w ((ObjectProperty.ι (KsubU (K1 ⊓ K2) trueCond)).op ⋙ presheafFunctor X C F) f ]
        apply eq_whisker
        rfl-/


/-instance truc4 : IsFiltered ((KsubU_cat K1 trueCond) × (KsubU_cat K2 trueCond)) ᵒᵖ := by
  exact isFiltered_op_of_isCofiltered (KsubU_cat K1 trueCond × KsubU_cat K2 trueCond)-/

#check small_lift

---variable [HasColimitsOfSize.{w} (Type z)]

instance truc5 : Small.{u} ((KsubU_cat K1 trueCond) × (KsubU_cat K2 trueCond)) ᵒᵖ := by

  sorry

variable (FF : TopCat.Sheaf (Type z) (of X))

#check colimitLimitIso (truc X _ FF K1 K2 ).flip








@[simps]
def AlphaUpFIsoColimFSubU : (FresSSK K (AlphaUpStar.obj ((Sheaf.forget C (of X)).obj F))) ≅ colimFia  (iaSubCEx K) (FcupIaEx K (presheafFunctor _ _ F)) where
  hom := ⟨fun _ => colimMap (eqToHom rfl),fun _ _ _ => by
    apply colimit.hom_ext
    intro
    simp [_root_.F]⟩
  inv := ⟨fun _ => colimMap (eqToHom rfl),fun _ _ _ => by
    apply colimit.hom_ext
    intro
    simp [_root_.F]⟩


@[simps]
def FLToKIsoToColimColim {K :Compacts X} : (FLToFK K (AlphaUpStar.obj ((Sheaf.forget C (of X)).obj F))) ≅ (Cocones.precomposeEquivalence (AlphaUpFIsoColimFSubU _ _ _ _ )).functor.obj (fCupIaCoconeToColimFiaCocone _ _ (colimit.cocone (FcupIaEx K (presheafFunctor _ _ F)))) where
  hom := ⟨𝟙 (colimit (FU K ((Sheaf.forget C (of X)).obj F) trueCond)), by aesop⟩
  inv := ⟨𝟙 (colimit (FcupIaEx K (presheafFunctor X C F))), by aesop⟩


@[simps!]
def shAlphaUpStarG : (Ksheaf X C) where
  carrier:= (AlphaUpStar).obj ((Sheaf.forget _ _).obj F)
  ksh1 := by
    have : IsTerminal ((F.val).obj (op (⊥ : Opens X))) := by
      apply Sheaf.isTerminalOfBotCover F (⊥ : Opens X)
      intro _ hx
      rcases hx
    apply IsTerminal.ofIso this
    apply @asIso _ _ _ _ _ (isIso_ι_of_isTerminal (TerminalOpBotsubU X) (FU ⊥ ((Sheaf.forget C (of X)).obj F) trueCond))
  ksh2 K1 K2 := by

    #check colimitLimitIso
    unfold AlphaUpStar AlphaUpStarP AlphaUpStarF
    unfold SquareSuptoInf
    #check Sheaf.isLimitPullbackCone F

    --simp
    sorry
  ksh3 K := by
    apply Limits.IsColimit.ofIsoColimit _ (FLToKIsoToColimColim  X _ _ ).symm
    apply IsColimit.ofPreservesCoconeInitial

    apply colimIsColimColim _ _ (repOEx K) (repHEx K) (repLiftingEx K) _
    exact colimit.isColimit (FcupIaEx K (presheafFunctor X C F))



@[simps]
def shAlphaUpStar : Sheaf C (of X) ⥤ (Ksheaf X C)  where
  obj G := shAlphaUpStarG X C G
  map f := (AlphaUpStar).map ((Sheaf.forget _ _).map f)


--Restrict the adjunction

def AdjShAlphaStar: (shAlphaUpStar X C ) ⊣ (shAlphaDownStar X C) := by
  apply (Adjunction.restrictFullyFaithful  (@AdjAlphaStar (of X) _ C _ _ _) _ _) _ _

  apply Sheaf.forget
  apply (inducedFunctor (fun (F:Ksheaf X C) => F.carrier))
  apply @Functor.FullyFaithful.ofFullyFaithful _ _ _ _ _ (TopCat.Sheaf.forget_full _ _) (TopCat.Sheaf.forgetFaithful _ _)

  apply fullyFaithfulInducedFunctor
  exact ⟨𝟙 _,𝟙 _,by aesop_cat,by aesop_cat⟩
  exact ⟨𝟙 _,𝟙 _,by aesop_cat,by aesop_cat⟩

--adjonction donne une équivalence de catégorie

#check IsIso ((Adjunction.unit (AdjShAlphaStar X C)).app F)

--variable  [ConcreteCategory C] [(forget C).ReflectsIsomorphisms ] [PreservesLimits (forget C)] [PreservesFilteredColimits (forget C)]
/- sur d'avoir besoin de tout ça?, en tout cas pour stalk iso functeur oui-/

/- c'est l'autre qu'il faut faire en premier-/
theorem IsoAlphaUnit :IsIso ((AdjShAlphaStar X C).unit.app F):= by
  /-have truc : ∀ (x : ↑(of X)), IsIso ((stalkFunctor C x).map ((AdjShAlphaStar X C).unit.app F).val):= by
    intro p
    rw [← Adjunction.homEquiv_id]
    simp

    sorry-/ -- soucis d'univers mais il faudrait se passer des stalks cf argument de joel riou
  sorry

  --apply Presheaf.isIso_of_stalkFunctor_map_iso


  --rw [← Adjunction.homEquiv_id]
  --#check (AdjShAlphaStar X C).unit.app F

  --#check ((𝟭 (TopCat.Sheaf C (of X))).obj F : Functor _ _)
  --#check NatTrans.isIso_iff_isIso_app ((AdjShAlphaStar X C).unit.app F)

  --sorry





  --apply asIso

  --unfold AdjShAlphaStar AdjAlphaStar
  --simp
  --#check (NatTrans.isIso_iff_isIso_app ((Adjunction.unit (AdjShAlphaStar X)).app F)).2

def machin : (𝟭 (Ksheaf X C)).obj G ⟶ (shAlphaDownStar X C ⋙ shAlphaUpStar X C).obj G  where
  app K := by
    simp
    sorry




#check (AdjShAlphaStar X C).counit.app G

theorem IsoAlphaCoUnit :IsIso ((AdjShAlphaStar X C).counit.app G):= by

  --unfold AdjShAlphaStar AlphaDownStar
  --simp


  --#check  TopCat.Presheaf.isIso_of_stalkFunctor_map_iso
  sorry


def KshIsoSh: (Sheaf C (of X)) ≌  (Ksheaf X C) := by
   apply @Adjunction.toEquivalence _ _ _ _  _  _ (AdjShAlphaStar X C) (IsoAlphaUnit X C) (IsoAlphaCoUnit X C)
