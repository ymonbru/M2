import M2.alpha_K_sheaf
import M2.lemmeTopologique

universe u v w

open CategoryTheory Limits TopologicalSpace Compacts Opposite Functor TopCat

variable {X Y : Type w} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]

variable {f : X → Y} (proper_f : IsProperMap f)

variable {C : Type u} [Category.{v, u} C]

/-- The inverse image of a proper map as functor over compacts -/
@[simps]
def preimageCompact : Compacts Y ⥤ Compacts X where
  obj K := ⟨f ⁻¹' K.carrier , IsProperMap.isCompact_preimage  proper_f K.isCompact'⟩
  map i := homOfLE (fun  _ ha => leOfHom i ha)

/-- The inverse image of a proper map as functor over compacts -/
@[simps!]
def preimageOpen : Opens Y ⥤ Opens X := (Opens.map (ofHom ( ContinuousMap.mk f proper_f.toContinuous)) )

variable ( F : (Compacts X)ᵒᵖ ⥤ C) (K : Compacts Y) [LocallyCompactSpace X]

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
  map f := ⟨(preimageCompact proper_f).map f.hom⟩



instance : (preimageResSubSub proper_f K).Initial := by
    apply (Functor.initial_iff_of_isCofiltered _).2
    constructor
    · intro L
      let closed_f := (IsProperMap.isClosedMap proper_f)

      use existsIntermedFrepKAndLCompact closed_f K L.obj.carrier (supSupKtoKsubInt _ L)

      apply Nonempty.intro
      constructor
      apply homOfLE
      exact existsIntermedFrepKAndLSpec closed_f K L.obj.carrier (supSupKtoKsubInt _ L)
    · intro _ U _ _
      use U
      use 𝟙 _
      rfl

variable [HasLimitsOfSize.{w, w} C] [HasColimitsOfSize.{w, w} C]

/-- the pushforward of a K-presheaf-/
@[simps!]
def fDownStar: ((Compacts X)ᵒᵖ ⥤ C) ⥤ (Compacts Y)ᵒᵖ ⥤ C :=
((whiskeringLeft _ _ _ ).obj (preimageCompact proper_f).op)

noncomputable section

/-- the pushforward of a KSheaf-/
@[simps]
def fDownStarFsh (F : Ksheaf X C) : Ksheaf Y C where
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
def KsheafPushforward : (Ksheaf X C ) ⥤ (Ksheaf Y C) where
  obj := fDownStarFsh proper_f
  map τ := ⟨fun _ => τ.hom.app _ ,by simp⟩

/-- The inverse image of a proper map as functor over neighbourhods of a compact K -/
@[simps]
def preimageRes : KsubU_cat K trueCond ⥤ KsubU_cat ((preimageCompact proper_f).obj K) trueCond where
  obj U := by
    use (preimageOpen proper_f).obj U.obj

    constructor
    exact Set.preimage_mono U.property.1
    rfl
  map f := ⟨(preimageOpen proper_f).map f.hom⟩

instance : (preimageRes proper_f K).Initial := by
    have :  IsCofilteredOrEmpty (KsubU_cat K trueCond) := by
      apply IsCofilteredKsubU
      simp
    apply (Functor.initial_iff_of_isCofiltered _).2
    constructor
    · intro U
      let closed_f := (IsProperMap.isClosedMap proper_f)

      have : f ⁻¹' ↑K ⊆ interior U.obj.carrier := by
        have : interior U.obj.carrier = U.obj.carrier := by
          refine interior_eq_iff_isOpen.mpr U.obj.isOpen
        rw [this]
        exact U.property.1

      let L := existsIntermedFrepKAndLCompact closed_f K U.obj.carrier this

      use supSupKToKsubU _ L

      apply Nonempty.intro
      constructor
      apply homOfLE

      apply Set.Subset.trans _ (existsIntermedFrepKAndLSpec closed_f K U.obj.carrier this)
      simp [preimageOpen, Opens.map]
      apply Set.preimage_mono
      exact (Classical.choose_spec L.property).2
    · intro _ U _ _
      use U
      use 𝟙 _
      rfl

variable (F : (Opens X)ᵒᵖ ⥤ C)

set_option backward.isDefEq.respectTransparency false in
/--For F a presheaf the natural transformation from f* α* F to α* f* F -/
@[simps]
def PushforwardCommAlphaUpF  : ((Presheaf.pushforward C (ofHom ⟨_ , proper_f.toContinuous⟩)).comp AlphaUpStar ).obj F ⟶ ((AlphaUpStar ).comp (fDownStar proper_f)).obj F  where
app K := (Functor.Final.colimitIso (preimageRes proper_f (unop K)).op (FU ((preimageCompact proper_f).obj (unop K)) (F) trueCond)).hom
naturality K1 K2 i:= by
  apply colimit.hom_ext
  intro U

  suffices colimit.ι (FU (unop K2) ((Presheaf.pushforward C (ofHom { toFun := f, continuous_toFun := _ })).obj F) trueCond)
      (op ((K1subK2subU trueCond i.unop).obj (unop U))) ≫
    (Final.colimitIso (preimageRes proper_f (unop K2)).op
        (FU ((preimageCompact proper_f).obj (unop K2)) F trueCond)).hom = colimit.ι (FU (unop K1) ((Presheaf.pushforward C (ofHom { toFun := f, continuous_toFun := _ })).obj F) trueCond) U ≫
    (Final.colimitIso (preimageRes proper_f (unop K1)).op
          (FU ((preimageCompact proper_f).obj (unop K1)) F trueCond)).hom ≫
      colimMap _ ≫ colimit.pre _ _ by simpa


  repeat rw [Functor.Final.colimitIso_hom]

  have : colimit.ι ((preimageRes proper_f (unop K2)).op ⋙ FU ((preimageCompact proper_f).obj (unop K2)) F trueCond) = colimit.ι (FU (unop K2) ((Presheaf.pushforward C (ofHom ⟨_ , proper_f.toContinuous⟩)).obj F) trueCond) := by
    rfl
  rw [← this, colimit.ι_pre, ← Category.assoc]

  have : colimit.ι (FU (unop K1) ((Presheaf.pushforward C (ofHom ⟨_ , proper_f.toContinuous⟩)).obj F) trueCond) = colimit.ι ((preimageRes proper_f (unop K1)).op ⋙ FU ((preimageCompact proper_f).obj (unop K1)) F trueCond) := by
    rfl

  rw [this, colimit.ι_pre]

  --aesop? --suggestion bizare?
  suffices colimit.ι _ (op ((preimageRes proper_f (unop K2)).obj ((K1subK2subU trueCond  i.unop).obj (unop U)))) = colimit.ι _ (op ((K1subK2subU trueCond (homOfLE _ )).obj ((preimageRes proper_f (unop K1)).obj (unop U)))) by simpa

  rfl

instance : IsIso (PushforwardCommAlphaUpF proper_f F) := by
  have : ∀ (K : (Compacts ↑(of Y))ᵒᵖ), IsIso ((PushforwardCommAlphaUpF proper_f F).app K) := by
    intro K
    exact Iso.isIso_hom _
  apply  NatIso.isIso_of_isIso_app

variable (C)

set_option backward.isDefEq.respectTransparency false in
/--The natural transformation from f* α* to α* f* over presheaves -/
@[simps]
def PushforwardCommAlphaUp  : (Presheaf.pushforward C (ofHom ⟨_ , proper_f.toContinuous⟩)).comp AlphaUpStar  ⟶ (AlphaUpStar ).comp (fDownStar proper_f) where
  app := PushforwardCommAlphaUpF proper_f
  naturality F G τ:= by
    apply NatTrans.ext
    ext K
    apply colimit.hom_ext
    intro U
    suffices τ.app (op ((Opens.map (ofHom { toFun := f, continuous_toFun := _ })).obj (unop U).obj)) ≫
    colimit.ι (FU (unop K) ((Presheaf.pushforward C (ofHom { toFun := f, continuous_toFun := _ })).obj G) trueCond) U ≫
      (Final.colimitIso (preimageRes proper_f (unop K)).op
          (FU ((preimageCompact proper_f).obj (unop K)) G trueCond)).hom =
  colimit.ι (FU (unop K) ((Presheaf.pushforward C (ofHom { toFun := f, continuous_toFun := _ })).obj F) trueCond) U ≫
    (Final.colimitIso (preimageRes proper_f (unop K)).op
          (FU ((preimageCompact proper_f).obj (unop K)) F trueCond)).hom ≫
      colimMap _ by simpa

    repeat rw [Functor.Final.colimitIso_hom]

    have : colimit.ι (FU (unop K) ((Presheaf.pushforward C (ofHom ⟨_ , proper_f.toContinuous⟩)).obj G) trueCond) = colimit.ι ((preimageRes proper_f (unop K)).op ⋙ FU ((preimageCompact proper_f).obj (unop K)) G trueCond) := by rfl

    rw [this, colimit.ι_pre]

    have : colimit.ι (FU (unop K) ((Presheaf.pushforward C (ofHom ⟨_ , proper_f.toContinuous⟩)).obj F) trueCond) = colimit.ι ((preimageRes proper_f (unop K)).op ⋙ FU ((preimageCompact proper_f).obj (unop K)) F trueCond) := by rfl

    rw [this, ← Category.assoc, colimit.ι_pre]

    simp
    rfl

instance : IsIso (PushforwardCommAlphaUp proper_f C) := by
  have : ∀ (F : Presheaf C (of X)), IsIso ((PushforwardCommAlphaUp proper_f C).app F) := by
    intro F
    suffices IsIso (PushforwardCommAlphaUpF proper_f F) by simpa
    exact instIsIsoFunctorOppositeCompactsCarrierOfPushforwardCommAlphaUpF proper_f F
  exact NatIso.isIso_of_isIso_app _

variable [AB5OfSize.{w, w, v, u} C]

/--The natural transformation from f* α* to α* f* for sheaves -/
@[simps]
def PushforwardCommAlphaUpShHom : (Sheaf.pushforward C (ofHom ⟨_ , proper_f.toContinuous⟩)).comp (shAlphaUpStar Y C) ⟶ (shAlphaUpStar X C).comp (KsheafPushforward proper_f) where
  app F := ⟨ (Functor.whiskerLeft (Sheaf.forget C (of X)) (PushforwardCommAlphaUp proper_f C)).app F⟩
  naturality _ _ τ := by
    apply InducedCategory.Hom.ext
    apply (PushforwardCommAlphaUp proper_f C).naturality

/--The inverse natural transformation from α* f* to f* α* for sheaves -/
@[simps]
def PushforwardCommAlphaUpShInv : (shAlphaUpStar X C).comp (KsheafPushforward proper_f) ⟶ (Sheaf.pushforward C (ofHom ⟨_ , proper_f.toContinuous⟩)).comp (shAlphaUpStar Y C) where
  app F := ⟨(Functor.whiskerLeft (Sheaf.forget C (of X)) ( inv (PushforwardCommAlphaUp proper_f C))).app F⟩
  naturality _ _ τ := by
    apply InducedCategory.Hom.ext
    apply (inv (PushforwardCommAlphaUp proper_f C)).naturality

set_option backward.isDefEq.respectTransparency false in
/--The natural isomorphism between  α* f* and f* α* for -/
@[simps]
def PushforwardCommAlphaUpSh : (Sheaf.pushforward C (ofHom ⟨_ , proper_f.toContinuous⟩)).comp (shAlphaUpStar Y C) ≅ (shAlphaUpStar X C).comp (KsheafPushforward proper_f) where
  hom := PushforwardCommAlphaUpShHom proper_f C
  inv := PushforwardCommAlphaUpShInv proper_f C
  hom_inv_id := by
    ext
    apply InducedCategory.Hom.ext
    simp [PushforwardCommAlphaUpShHom, PushforwardCommAlphaUpShInv]
    rw [InducedCategory.comp_hom]-- c'est fou qu'il ai besoin d'aide à ce point avec 27 et 28
    simp
    rfl
  inv_hom_id := by
    ext
    apply InducedCategory.Hom.ext
    simp [PushforwardCommAlphaUpShHom, PushforwardCommAlphaUpShInv]
    rw [InducedCategory.comp_hom]-- c'est fou qu'il ai besoin d'aide à ce point avec 27 et 28
    simp
    rfl

#lint
#min_imports
