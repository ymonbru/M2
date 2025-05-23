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

open CategoryTheory Limits TopologicalSpace TopologicalSpace.Compacts Opposite TopCat TopCat.Presheaf
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
def truc2 (U : (KsubU_cat K1 trueCond) × (KsubU_cat K2 trueCond)) : WalkingCospan ⥤ (Opens X) ᵒᵖ  where
  obj x := match x with
    |.left => op U.1.obj
    |.right => op  U.2.obj
    |.one => op (U.1.obj ⊓ U.2.obj)
  map {x y } f :=
    match f with
      | WalkingCospan.Hom.inl => op (homOfLE inf_le_left)
      | WalkingCospan.Hom.inr => op (homOfLE inf_le_right)
      | WalkingCospan.Hom.id z => op (𝟙 _)

@[simps]
def truc3 {U V : (KsubU_cat K1 trueCond) × (KsubU_cat K2 trueCond)} (f : U ⟶ V) : truc2 _ _ _ V ⟶ truc2 _ _ _ U where
  app x := match x with
    |.left => op f.1
    |.right => op f.2
    |.one => op (homOfLE (inf_le_inf (leOfHom f.1) (leOfHom f.2)))

@[simps]
def truc : ((KsubU_cat K1 trueCond) × (KsubU_cat K2 trueCond)) ᵒᵖ  ⥤ (WalkingCospan ⥤ C) where
  obj U := truc2 _ _ _ U.unop ⋙  presheafFunctor _ _ F
  map {U V} f:= whiskerRight (truc3 _ _ _ f.unop) (presheafFunctor X C F)
  map_id _ := by
    ext x
    match x with
    | _ =>
      suffices (presheafFunctor X C F).map _ = 𝟙 _ by simpa
      rw [← (presheafFunctor X C F).map_id]
      rfl
  map_comp f g := by
    ext x
    match x with
      | _ =>
        suffices (presheafFunctor X C F).map _ = (presheafFunctor X C F).map _ ≫ (presheafFunctor X C F).map _ by simpa
        rw [← (presheafFunctor X C F).map_comp]
        rfl

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


variable [UnivLE.{w, z}]
variable (G : Ksheaf X (Type z)) (F : Sheaf (Type z) (of X))


#check colimitLimitIso (truc X _ F K1 K2 ).flip

def bidule2ι : (truc X (Type z) F K1 K2).flip.flip ⟶ (Functor.const (KsubU_cat K1 trueCond × KsubU_cat K2 trueCond)ᵒᵖ).obj (cospan (FtoFInfLeft (AlphaUpStar.obj ((Sheaf.forget (Type z) (of X)).obj F)) K1 K2) (FtoFInfRight (AlphaUpStar.obj ((Sheaf.forget (Type z) (of X)).obj F)) K1 K2)) where
  app U := by
    simp [Functor.flip_flip]
    have trucs : (truc X (Type z) F K1 K2).flip.flip.obj U := by sorry
    simp at trucs
    beta_reduce
    dsimp
    simp [AlphaUpStar, AlphaUpStarF]
    aesop
    sorry
  naturality := sorry


def bidule2 : Cocone ((truc X (Type z) F K1 K2).flip.flip) where
  pt := cospan (FtoFInfLeft (AlphaUpStar.obj ((Sheaf.forget (Type z) (of X)).obj F)) K1 K2)
    (FtoFInfRight (AlphaUpStar.obj ((Sheaf.forget (Type z) (of X)).obj F)) K1 K2)
  ι := by
    simp
    sorry

def bidule : (colimit (truc X (Type z) F K1 K2).flip.flip) ⟶  cospan (FtoFInfLeft (AlphaUpStar.obj ((Sheaf.forget (Type z) (of X)).obj F)) K1 K2) (FtoFInfRight (AlphaUpStar.obj ((Sheaf.forget (Type z) (of X)).obj F)) K1 K2) := by
  apply colimit.desc
  sorry

#check (SquareSuptoInf (AlphaUpStar.obj ((Sheaf.forget (Type z) (of X)).obj F)) K1 K2)




@[simps!]
def shAlphaUpStarG : (Ksheaf X (Type z)) where
  carrier:= (AlphaUpStar).obj ((Sheaf.forget _ _).obj F)
  ksh1 := by
    have : IsTerminal ((F.val).obj (op (⊥ : Opens X))) := by
      apply Sheaf.isTerminalOfBotCover F (⊥ : Opens X)
      intro _ hx
      rcases hx
    apply IsTerminal.ofIso this
    apply @asIso _ _ _ _ _ (isIso_ι_of_isTerminal (TerminalOpBotsubU X) (FU ⊥ ((Sheaf.forget (Type z) (of X)).obj F) trueCond))
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
    exact colimit.isColimit (FcupIaEx K (presheafFunctor X (Type z) F))



@[simps]
def shAlphaUpStar : Sheaf (Type z) (of X) ⥤ (Ksheaf X (Type z))  where
  obj G := shAlphaUpStarG X G
  map f := (AlphaUpStar).map ((Sheaf.forget _ _).map f)


--Restrict the adjunction

def AdjShAlphaStar: (shAlphaUpStar X ) ⊣ (shAlphaDownStar X (Type z)) := by
  apply (Adjunction.restrictFullyFaithful  (@AdjAlphaStar (of X) _ (Type z) _ _ _) _ _) _ _

  apply Sheaf.forget
  apply (inducedFunctor (fun (F:Ksheaf X (Type z)) => F.carrier))
  apply @Functor.FullyFaithful.ofFullyFaithful _ _ _ _ _ (TopCat.Sheaf.forget_full _ _) (TopCat.Sheaf.forgetFaithful _ _)

  apply fullyFaithfulInducedFunctor
  exact ⟨𝟙 _,𝟙 _,by aesop_cat,by aesop_cat⟩
  exact ⟨𝟙 _,𝟙 _,by aesop_cat,by aesop_cat⟩

--adjonction donne une équivalence de catégorie

#check IsIso ((Adjunction.unit (AdjShAlphaStar X )).app F)

--variable  [ConcreteCategory C] [(forget C).ReflectsIsomorphisms ] [PreservesLimits (forget C)] [PreservesFilteredColimits (forget C)]
/- sur d'avoir besoin de tout ça?, en tout cas pour stalk iso functeur oui-/

/- c'est l'autre qu'il faut faire en premier-/
theorem IsoAlphaUnit :IsIso ((AdjShAlphaStar X ).unit.app F):= by
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

def machin : (𝟭 (Ksheaf X (Type z))).obj G ⟶ (shAlphaDownStar X (Type z) ⋙ shAlphaUpStar X ).obj G  where
  app K := by
    simp
    sorry




#check (AdjShAlphaStar X ).counit.app G

theorem IsoAlphaCoUnit :IsIso ((AdjShAlphaStar X ).counit.app G):= by

  --unfold AdjShAlphaStar AlphaDownStar
  --simp


  --#check  TopCat.Presheaf.isIso_of_stalkFunctor_map_iso
  sorry


def KshIsoSh: (Sheaf (Type z) (of X)) ≌  (Ksheaf X (Type z)) := by
   apply @Adjunction.toEquivalence _ _ _ _  _  _ (AdjShAlphaStar X ) (IsoAlphaUnit X ) (IsoAlphaCoUnit X )
