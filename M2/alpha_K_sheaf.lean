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

@[simps]
def natTransCospan {C : Type u} [Category.{v} C] { A1 B1 C1 A2 B2 C2 : C} { f1 : A1 ⟶ B1} { g1 : C1 ⟶ B1} { f2 : A2 ⟶ B2} { g2 : C2 ⟶ B2} (a : A1 ⟶ A2) (b : B1 ⟶ B2) (c : C1 ⟶ C2) (hab : f1 ≫ b = a ≫ f2) (hbc : g1 ≫ b = c ≫ g2):  cospan f1 g1 ⟶ cospan f2 g2 where
  app x := match x with
    |.left => a
    |.right => c
    |.one => b
  naturality  x y f := match f with
    | WalkingCospan.Hom.inl => hab
    | WalkingCospan.Hom.inr => hbc
    | WalkingCospan.Hom.id _ => by simp


@[simps]
def truc9 : ((KsubU_cat K1 trueCond) × (KsubU_cat K2 trueCond) )ᵒᵖ  ⥤ WalkingCospan ⥤ (Opens X)ᵒᵖ where
  obj U := cospan (op (homOfLE inf_le_left): op U.unop.1.obj ⟶ op (U.unop.1.obj ⊓ U.unop.2.obj) ) (op (homOfLE inf_le_right ): op U.unop.2.obj ⟶ op (U.unop.1.obj ⊓ U.unop.2.obj))
  map {U V} f := natTransCospan (op f.unop.1) (op (subK1SubK2toSubK1InterK2.map f.unop)) (op f.unop.2) (rfl) (rfl)

@[simps!]
def truc : ((KsubU_cat K1 trueCond) × (KsubU_cat K2 trueCond)) ᵒᵖ ⥤ (WalkingCospan ⥤ C) := let WToOInWToC := (whiskeringRight WalkingCospan _ _ ).obj (presheafFunctor _ _ F); ((whiskeringRight (KsubU_cat K1 trueCond × KsubU_cat K2 trueCond)ᵒᵖ _ _).obj  WToOInWToC).obj (truc9 X K1 K2)


@[simps!]
def truc4Pt : WalkingCospan ⥤ C := by
  apply cospan
  exact colimit.pre (Functor.op  (ObjectProperty.ι _ ) ⋙ presheafFunctor X C F) (Functor.op ( K1subK2subU trueCond (homOfLE (inf_le_left) : K1 ⊓ K2 ⟶ K1)))
  exact colimit.pre (Functor.op  (ObjectProperty.ι _ ) ⋙ presheafFunctor X C F) (Functor.op ( K1subK2subU trueCond (homOfLE (inf_le_right) : K1 ⊓ K2 ⟶ K2)))

@[simps]
def truc4ι : truc X C F K1 K2 ⟶ (Functor.const (KsubU_cat K1 trueCond × KsubU_cat K2 trueCond)ᵒᵖ).obj (truc4Pt X C F K1 K2) where
  app U := by
    apply (cospanCompIso _ _ _).hom ≫ _

    refine natTransCospan ?_ ?_ ?_ ?_ ?_
    · exact colimit.ι ((K1subK2subU trueCond (homOfLE inf_le_left)).op ⋙ (ObjectProperty.ι (KsubU (K1 ⊓ K2) trueCond)).op ⋙ presheafFunctor X C F) (op U.unop.1)
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
      simp
  naturality U V f:= by
    ext x
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
        rw [ ← colimit.w _ this ]
        rfl
@[simps]
def truc4 : Cocone (truc X C F K1 K2 ) where
  pt := truc4Pt X C F K1 K2
  ι := truc4ι X C F K1 K2

variable (s : Cocone (truc X C F K1 K2)) (x : WalkingCospan)

instance : Top (KsubU_cat K1 trueCond) where
  top := by
    use ⊤
    simp

def truc4DescCoconeLeftι : (K1subK2subU trueCond (homOfLE inf_le_left)).op ⋙ (ObjectProperty.ι (KsubU (K1 ⊓ K2) trueCond)).op ⋙ presheafFunctor X C F ⟶ (Functor.const (KsubU_cat K1 trueCond)ᵒᵖ).obj (s.pt.obj .left) where
  app U := (s.ι.app  (op ⟨U.unop, ⊤⟩)).app .left
  naturality U V f:= by
    suffices (presheafFunctor X C F).map (homOfLE _).op ≫ (s.ι.app (op (unop V, ⊤))).app WalkingCospan.left = (s.ι.app (op (unop U, ⊤))).app WalkingCospan.left by simpa
    have : ((truc X C F K1 K2).obj (op (unop U, ⊤))).map (WalkingCospan.Hom.id WalkingCospan.left) ≫ (s.ι.app (op (unop U, ⊤))).app WalkingCospan.left = (s.ι.app (op (unop U, ⊤))).app WalkingCospan.left := by
      rw [(s.ι.app (op (unop U, ⊤))).naturality (WalkingCospan.Hom.id .left)]
      simp
    rw [← this]

    have : (truc X C F K1 K2).map (op (f.unop, 𝟙 ⊤)) ≫ s.ι.app (op (unop V, ⊤)) = s.ι.app (op (unop U, ⊤)) := by
      rw [s.ι.naturality ((op ⟨f.unop, 𝟙 _⟩) : (op ⟨U.unop, ⊤⟩) ⟶ (op ⟨V.unop, ⊤⟩))]
      simp
    rw [← this]
    suffices (presheafFunctor X C F).map (homOfLE (leOfHom f.unop)).op ≫ (s.ι.app (op (unop V, ⊤))).app WalkingCospan.left = (presheafFunctor X C F).map (op f.unop) ≫ (s.ι.app (op (unop V, ⊤))).app WalkingCospan.left by simpa [truc]

    rfl


def truc4DescCoconeLeft : Cocone ((K1subK2subU trueCond (homOfLE inf_le_left)).op ⋙ (ObjectProperty.ι (KsubU (K1 ⊓ K2) trueCond)).op ⋙ presheafFunctor X C F) where
  pt := s.pt.obj .left
  ι := truc4DescCoconeLeftι X C F K1 K2 s

def truc4Desc : truc4Pt X C F K1 K2 ⟶ s.pt where
  app x := match x with
    | .left => colimit.desc _ (truc4DescCoconeLeft _ _ _ _ _ _)
    | _ => sorry


def truc4Colim : IsColimit (truc4 X C F K1 K2) where
  desc s := by
    simp

    apply?
    sorry


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
