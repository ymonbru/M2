import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Topology.Sets.Compacts
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Sheaves.Functors
--import M2.Ksheaves
import M2.alpha_K_sheaf
--import M2.RCalpha

open CategoryTheory Limits TopologicalSpace Compacts Opposite Functor TopCat


variable {X Y} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]

variable {f : X → Y} (proper_f : IsProperMap f)

/-- The inverse image of a proper map as functor over compacts -/
@[simps]
def preimageCompact : Compacts Y ⥤ Compacts X where
  obj K := ⟨f ⁻¹' K.carrier , IsProperMap.isCompact_preimage  proper_f K.isCompact'⟩
  map i := homOfLE (fun  _ ha => leOfHom i ha)

/-- The inverse image of a proper map as functor over compacts -/
@[simps!]
def preimageOpen : Opens Y ⥤ Opens X := (Opens.map (ofHom ( ContinuousMap.mk f proper_f.toContinuous)) )



variable {C} [Category C]
variable ( F : (Compacts X)ᵒᵖ ⥤ C) (K : Compacts Y) --[LocallyCompactSpace X]

/-def preimageRes : RelCN_cat K ⥤ RelCN_cat ((preimageCompact proper_f).obj K) where
  obj U := by
    use (preimageOpen proper_f).obj U.obj

    constructor
    exact Set.preimage_mono U.property.1
    exact IsCompact.of_isClosed_subset (IsProperMap.isCompact_preimage proper_f U.property.2) isClosed_closure (Continuous.closure_preimage_subset (proper_f.toContinuous) U.obj.carrier)
  map _ := (preimageOpen proper_f).map _

instance : (preimageRes proper_f K).Initial := by
    apply (Functor.initial_iff_of_isCofiltered _).2
    constructor
    · intro U
    --lemme de topologie de Pardon
      sorry
    · intro _ U _ _
      use U
      use 𝟙 _
      rfl-/

/-- The inverse image of a proper map as functor over compacts that contain K in their interior -/
@[simps]
def preimageResSubSub : supSupK_cat K ⥤ supSupK_cat ((preimageCompact proper_f).obj K) where
  obj L := by
    use (preimageCompact proper_f).obj L.obj
    rcases L.property with ⟨U, hU1, hU2⟩
    use (preimageOpen proper_f).obj U
    constructor
    · intro _ ha
      exact hU1 ha
    · intro _ ha
      exact hU2 ha
  map _ := (preimageCompact proper_f).map _


instance : (preimageResSubSub proper_f K).Initial := by
    apply (Functor.initial_iff_of_isCofiltered _).2
    constructor
    · intro L
    --lemme de topologie de Pardon
    --visiblement c'est plus compliqué que juste appliquer le lemme..

      sorry
    · intro _ U _ _
      use U
      use 𝟙 _
      rfl

variable [HasLimits C] [HasColimits C]

/-- the pushforward of a K-presheaf-/
def fDownStar: ((Compacts X)ᵒᵖ ⥤ C) ⥤ (Compacts Y)ᵒᵖ ⥤ C :=
((whiskeringLeft _ _ _ ).obj (preimageCompact proper_f).op)

/-- the pushforward of a KSheaf-/
@[simps]
noncomputable def fDownStarFsh (F : Ksheaf X C) : Ksheaf Y C where
  carrier := (fDownStar proper_f).obj F.carrier
  ksh1 := by
    exact F.ksh1
  ksh2 := by
    intro _ _
    exact F.ksh2 ((preimageCompact proper_f).obj _) ((preimageCompact proper_f).obj _)
  ksh3 := by
    intro K
    let K' := (preimageCompact proper_f).obj K
    exact (Functor.Final.isColimitWhiskerEquiv ((preimageResSubSub proper_f K).op) ((FLToFK K' F.carrier))).invFun (F.ksh3 K')

/-- Pushforward of KSheaf as a functor-/
@[simps]
noncomputable def KsheafPushforward : (Ksheaf X C ) ⥤ (Ksheaf Y C) where
  obj := fDownStarFsh proper_f
  map := by
    intro _ _ τ
    constructor
    intro _ _ _
    apply τ.naturality

/-- The inverse image of a proper map as functor over neighbourhods of a compact K -/
@[simps]
def preimageRes : KsubU_cat K trueCond ⥤ KsubU_cat ((preimageCompact proper_f).obj K) trueCond where
  obj U := by
    use (preimageOpen proper_f).obj U.obj

    constructor
    exact Set.preimage_mono U.property.1
    rfl
  map _ := (preimageOpen proper_f).map _

instance : (preimageRes proper_f K).Initial := by
    have :  IsCofilteredOrEmpty (KsubU_cat K trueCond) := by
      apply IsCofilteredKsubU
      simp
    apply (Functor.initial_iff_of_isCofiltered _).2
    constructor
    · intro U
      -- lemme de topologie de Pardon
      sorry
    · intro _ U _ _
      use U
      use 𝟙 _
      rfl



-- A partir de la c'est des expériences

variable (F : (Opens X)ᵒᵖ ⥤ C)

noncomputable def truc  : ((Presheaf.pushforward C (ofHom ⟨_ , proper_f.toContinuous⟩)).comp AlphaUpStar ).obj F ⟶ ((AlphaUpStar ).comp (fDownStar proper_f)).obj F  where
app K := (Functor.Final.colimitIso (preimageRes proper_f (unop K)).op (FU ((preimageCompact proper_f).obj (unop K)) (F) trueCond)).hom
naturality K1 K2 i:= by
  simp
  repeat rw [Functor.Final.colimitIso_hom]
  apply colimit.hom_ext
  intro U
  simp

  #check colimit.ι_pre (FU ((preimageCompact proper_f).obj (unop K1)) (F) trueCond) ((preimageRes proper_f (unop K2)).comp (K1subK2subU trueCond _ _ _)).op (op ((K1subK2subU trueCond (unop K2) (unop K1) i.unop).obj (unop U)))





  rw [← Category.assoc]




  --rw [← CategoryTheory.Limits.colimit.ι_pre]
  sorry

def truc  : (fDownStar.comp ((AlphaUpStar (of Y) C)).obj F) ⟶ (AlphaUpStar (of X) C).comp (fDownStarF F) := by

  #check (Functor.Final.colimitIso (preimageRes proper_f (unop K)).op (FU ((preimageCompact proper_f).obj (unop K)) ((Sheaf.forget C (of X)).obj F) trueCond)).hom

  sorry














variable (F : TopCat.Sheaf C (of X))
#check (Functor.Final.colimitIso (preimageRes proper_f (K)).op (FU ((preimageCompact proper_f).obj (K)) ((Sheaf.forget C (of X)).obj F) trueCond))

variable (K1 K2 : Compacts Y ) (i : K1 ⟶ K2)


lemma heyho : (K1subK2subU trueCond K1 K2 i).comp (preimageRes proper_f K1) = (preimageRes proper_f K2).comp (K1subK2subU trueCond _ _ ((preimageCompact proper_f).map i)) := by
  rfl
  --sorry

noncomputable def truc0 (F : TopCat.Sheaf C (of X)) : ((Sheaf.pushforward C (ofHom ⟨_ , proper_f.toContinuous⟩)).comp (shAlphaUpStar (of Y) C)).obj F ⟶ ((shAlphaUpStar (of X) C).comp (KsheafPushforward proper_f)).obj F where
  app K := (Functor.Final.colimitIso (preimageRes proper_f (unop K)).op (FU ((preimageCompact proper_f).obj (unop K)) ((Sheaf.forget C (of X)).obj F) trueCond)).hom
  naturality := by
    intro K1 K2 i
    simp
    repeat rw [Functor.Final.colimitIso_hom]
    apply colimit.hom_ext
    intro U
    simp

    --#check colimit.ι_pre (FU ((preimageCompact proper_f).obj (unop K1)) ((Sheaf.forget C (of X)).obj F) trueCond) (preimageRes proper_f (unop K2)).op (op ((K1subK2subU trueCond (unop K2) (unop K1) i.unop).obj (unop U)))





    rw [← Category.assoc]




    --rw [← CategoryTheory.Limits.colimit.ι_pre]





    sorry

def truc1 : (Sheaf.pushforward C (ofHom ⟨_ , proper_f.toContinuous⟩)).comp (shAlphaUpStar (of Y) C) ⟶ (shAlphaUpStar (of X) C).comp (KsheafPushforward proper_f) where
  app F : _ := by
    simp

    sorry
  naturality := sorry


lemma truc : (KsheafPushforward proper_f).comp (shAlphaDownStar (of Y) C) = (shAlphaDownStar (of X) C).comp (Sheaf.pushforward C (ofHom ⟨_ , proper_f.toContinuous⟩)) := by
  #check (Sheaf.forget C ( of X) )
  have : ((KsheafPushforward proper_f).comp (shAlphaDownStar (of Y) C)).comp (Sheaf.forget C ( of Y) ) = ((shAlphaDownStar (of X) C).comp (Sheaf.pushforward C (ofHom ⟨_ , proper_f.toContinuous⟩))).comp (Sheaf.forget C ( of Y) ) := by sorry

  aesop?
  apply CategoryTheory.Functor.ext
  · intro F G τ
    apply Sheaf.Hom.ext
    ext U
    --unfold shAlphaDownStar
    simp
    sorry
  · intro F

    --simp

    sorry

lemma hey (F  G : Sheaf C (of X)) (h : F.val = G.val): F = G := by
  aesop
  sorry

    /-
  ext
  apply CategoryTheory.Functor.ext
  #check (KsheafPushforward proper_f ⋙ shAlphaDownStar (↑(of Y)) C).map τ

  simp
  unfold shAlphaDownStar shAlphaDownStarF AlphaDownStar AlphaDownStarG
  simp
  unfold AlphaDownStarSigma KsheafPushforward
  simp


  sorry-/

def machine : (of X) ⟶ (of Y) := by
  apply ofHom ⟨_ , proper_f.toContinuous⟩

  --sorry
