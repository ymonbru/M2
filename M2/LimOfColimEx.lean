import M2.KsubU
import M2.LimOfColimEqColimOfLim

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite --TopCat TopCat.Presheaf
--open ZeroObject

noncomputable section

universe u v w z

variable {X : Type w} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
variable {C : Type u} [Category.{v, u} C] [HasLimitsOfSize.{w,w} C] [HasColimitsOfSize.{w,w} C]

variable (F : (Opens X)ᵒᵖ ⥤ C) (K1 K2 : Compacts X)

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
def UInterWC : ((KsubU_cat K1 trueCond) × (KsubU_cat K2 trueCond) )ᵒᵖ  ⥤ WalkingCospan ⥤ (Opens X)ᵒᵖ where
  obj U := cospan (op (homOfLE inf_le_left): op U.unop.1.obj ⟶ op (U.unop.1.obj ⊓ U.unop.2.obj) ) (op (homOfLE inf_le_right ): op U.unop.2.obj ⟶ op (U.unop.1.obj ⊓ U.unop.2.obj))
  map {U V} f := natTransCospan (op f.unop.1) (op (subK1SubK2toSubK1InterK2.map f.unop)) (op f.unop.2) (rfl) (rfl)

/-- The left projection: (K1 ⊆ U1, K2 ⊆ U) ↦ U1-/
@[simps!]
def jLeft : ((KsubU_cat K1 trueCond) × (KsubU_cat K2 trueCond) )ᵒᵖ ⥤ (Opens X)ᵒᵖ := (UInterWC K1 K2).flip.obj .left

/-- The Right projection: (K1 ⊆ U1, K2 ⊆ U) ↦ U2-/
@[simps!]
def jRight : ((KsubU_cat K1 trueCond) × (KsubU_cat K2 trueCond) )ᵒᵖ ⥤ (Opens X)ᵒᵖ := ( UInterWC K1 K2).flip.obj .right

/-- The "intersection" projection: (K1 ⊆ U1, K2 ⊆ U) ↦ U1 ∩ U2-/
@[simps!]
def jOne : ((KsubU_cat K1 trueCond) × (KsubU_cat K2 trueCond) )ᵒᵖ ⥤ (Opens X)ᵒᵖ := ( UInterWC K1 K2).flip.obj .one

/-- The "union" projection: (K1 ⊆ U1, K2 ⊆ U) ↦ U1 ∩ U2-/
@[simps!]
def jCup : ((KsubU_cat K1 trueCond) × (KsubU_cat K2 trueCond) )ᵒᵖ ⥤ (Opens X)ᵒᵖ where
  obj U := op (U.unop.1.obj ⊔ U.unop.2.obj)
  map f := op (homOfLE (sup_le_sup (leOfHom f.unop.1) (leOfHom f.unop.2)
))

/-- The obvious natural transformation from jLeft to jOne -/
def jLToJO : (jLeft K1 K2) ⟶ (jOne K1 K2) where
  app U := op (homOfLE (by simp))

/-- The obvious natural transformation from jRight to jOne-/
def jRToJO : (jRight K1 K2) ⟶ (jOne K1 K2) where
  app U := op (homOfLE (by simp))

/-- The obvious natural transformation from jLeft to jOne -/
def jCToJL : (jCup K1 K2) ⟶ (jLeft K1 K2)  where
  app U := op (homOfLE (by simp))

/-- The obvious natural transformation from jRight to jOne-/
def jCToJR : (jCup K1 K2) ⟶ (jRight K1 K2) where
  app U := op (homOfLE (by simp))

/-- Whiskering UInterWC by F: For any pair U1 U2 (containing K1 and K2) the diagram F(U1) → F(U1 ∩ U2) ← U2 in a functorial way-/
@[simps!]
def FUInterWC : ((KsubU_cat K1 trueCond) × (KsubU_cat K2 trueCond)) ᵒᵖ ⥤ (WalkingCospan ⥤ C) := let WToOInWToC := (whiskeringRight WalkingCospan _ _ ).obj F; ((whiskeringRight (KsubU_cat K1 trueCond × KsubU_cat K2 trueCond)ᵒᵖ _ _).obj  WToOInWToC).obj ( UInterWC K1 K2)

/-- The diaram colimit_{K1 ⊆ U}F(U) → colimit_{K1 ∩ K2 ⊆ U}F(U) ← colimit_{K2 ⊆ U} F(U)-/
@[simps!]
def colimFUInterWCPt : WalkingCospan ⥤ C := by
  apply cospan
  exact colimMap ( whiskerRight (jLToJO K1 K2) F)
  exact colimMap ( whiskerRight (jRToJO K1 K2) F)

/-- the natural transformation that makes colimFUInterWCPt a Cocone over truc-/
@[simps]
def colimFUInterWCι : FUInterWC F K1 K2 ⟶ (Functor.const (KsubU_cat K1 trueCond × KsubU_cat K2 trueCond)ᵒᵖ).obj (colimFUInterWCPt F K1 K2) where
  app U := by
    apply (cospanCompIso _ _ _).hom ≫ _
    refine natTransCospan ?_ ?_ ?_ ?_ ?_
    · exact colimit.ι (jLeft K1 K2 ⋙ F) U
    · exact colimit.ι (jOne K1 K2 ⋙ F) U
    · exact colimit.ι (jRight K1 K2 ⋙ F) U
    · suffices F.map (op (homOfLE _)) ≫ colimit.ι (jOne K1 K2 ⋙ F) U = F.map ((jLToJO K1 K2).app U) ≫ colimit.ι (jOne K1 K2 ⋙ F) U by simpa
      rfl
    · suffices F.map (op (homOfLE _)) ≫ colimit.ι (jOne K1 K2 ⋙ F) U = F.map ((jRToJO K1 K2).app U) ≫ colimit.ι (jOne K1 K2 ⋙ F) U by simpa
      rfl
  naturality U V f:= by
    ext x
    match x with
      | .left =>
        suffices F.map (op f.unop.1) ≫ colimit.ι (jLeft K1 K2 ⋙ F) V = colimit.ι (jLeft K1 K2 ⋙ F) U by simpa
        rw [← colimit.w _ f]
        rfl
      | .right =>
        suffices F.map (op f.unop.2) ≫ colimit.ι (jRight K1 K2 ⋙ F) V = colimit.ι (jRight K1 K2 ⋙ F) U by simpa
        rw [← colimit.w _ f]
        rfl
      | .one =>
        simp
        rw [← colimit.w _ f]
        rfl

/-- The cocne structre of colimFUInterWCPt over truc-/
@[simps]
def colimFUInterWC : Cocone (FUInterWC F K1 K2 ) where
  pt := colimFUInterWCPt F K1 K2
  ι := colimFUInterWCι F K1 K2

variable (s : Cocone (FUInterWC F K1 K2)) (x : WalkingCospan)

@[simps]
def colimFUInterWCDescCoconeXι (j : ((KsubU_cat K1 trueCond) × (KsubU_cat K2 trueCond) )ᵒᵖ ⥤ (Opens X)ᵒᵖ ) (h : ∀ U, unop ((( UInterWC K1 K2).obj U).obj x) ≤ unop (j.obj U)
 ): j ⋙ F ⟶ (Functor.const _).obj (s.pt.obj x) where
  app U := F.map ( op (homOfLE (h U))) ≫ (s.ι.app  U).app x
  naturality U V f:= by
    suffices F.map (j.map f) ≫ F.map (op (homOfLE _)) ≫ (s.ι.app V).app x = F.map (op (homOfLE _)) ≫ (s.ι.app U).app x by simpa

    have : (FUInterWC F K1 K2).map f ≫ s.ι.app V = s.ι.app U := by
      rw [ s.ι.naturality f]
      simp
    rw [← this, ← Category.assoc, ← F.map_comp]

    suffices _ ≫ _ = _ ≫_ ≫ _ by dsimp; assumption
    rw [← Category.assoc, ← F.map_comp]
    rfl

@[simps]
def colimFUInterWCDescCoconeX (j : ((KsubU_cat K1 trueCond) × (KsubU_cat K2 trueCond) )ᵒᵖ ⥤ (Opens X)ᵒᵖ ) (h : ∀ U, unop ((( UInterWC K1 K2).obj U).obj x) ≤ unop (j.obj U)
 ): Cocone (j ⋙ F) where
  pt := s.pt.obj x
  ι := colimFUInterWCDescCoconeXι F K1 K2 s x j h

@[simps!]
def colimFUInterWCDesc : colimFUInterWCPt F K1 K2 ⟶ s.pt := by
  refine natTransWcspFunc _ _ ?_ ?_ ?_ ?_ ?_
  · exact colimit.desc _ (colimFUInterWCDescCoconeX _ _ _ _ .left (jLeft K1 K2)  (fun _ => by simp))
  · exact colimit.desc _ (colimFUInterWCDescCoconeX _ _ _ _ .right (jRight K1 K2)  (by simp))
  · exact colimit.desc _ (colimFUInterWCDescCoconeX  _ _ _ _ .one (jOne K1 K2)  (by simp))

  · apply colimit.hom_ext
    intro U
    suffices F.map ((jLToJO K1 K2).app U) ≫ F.map (op (𝟙 ((unop U).1.obj ⊓ (unop U).2.obj))) ≫ (s.ι.app U).app WalkingCospan.one = F.map (op (𝟙 (unop U).1.obj)) ≫ (s.ι.app U).app WalkingCospan.left ≫ s.pt.map WalkingCospan.Hom.inl by simpa

    have : F.map (op (homOfLE ( UInterWC._proof_2 K1 K2 U))) ≫ (s.ι.app U).app WalkingCospan.one = (s.ι.app U).app WalkingCospan.left ≫ s.pt.map WalkingCospan.Hom.inl := by
      exact (s.ι.app U).naturality WalkingCospan.Hom.inl
    rw [← this]

    suffices _ ≫ _ ≫ _ = _ ≫_ ≫ _ by dsimp; assumption
    rw [← Category.assoc, ← F.map_comp, ← Category.assoc, ← F.map_comp]
    rfl
  · apply colimit.hom_ext
    intro U
    suffices F.map ((jRToJO K1 K2).app U) ≫
    F.map (op (𝟙 ((unop U).1.obj ⊓ (unop U).2.obj))) ≫ (s.ι.app U).app WalkingCospan.one = F.map (op (𝟙 (unop U).2.obj)) ≫
    (s.ι.app U).app WalkingCospan.right ≫ s.pt.map WalkingCospan.Hom.inr by simpa
    have : F.map (op (homOfLE ( UInterWC._proof_3 K1 K2 U))) ≫ (s.ι.app U).app WalkingCospan.one = (s.ι.app U).app WalkingCospan.right ≫ s.pt.map WalkingCospan.Hom.inr := by
      exact (s.ι.app U).naturality WalkingCospan.Hom.inr
    rw [← this]

    suffices _ ≫ _ ≫ _ = _ ≫_ ≫ _ by dsimp; assumption
    rw [← Category.assoc, ← F.map_comp, ← Category.assoc, ← F.map_comp]
    rfl

@[simps]
def colimFUInterWCColim : IsColimit (colimFUInterWC F K1 K2) where
  desc s := colimFUInterWCDesc F K1 K2 s
  fac s U := by
    ext x
    match x with
      | .left =>
        suffices F.map (op (𝟙 (unop U).1.obj)) ≫ (s.ι.app U).app WalkingCospan.left = (s.ι.app U).app WalkingCospan.left by simpa
        suffices op (𝟙 (unop U).1.obj) = 𝟙 ((op U.unop.1.obj))  by
          rw [this]
          simp
        rfl
      | .right =>
        suffices F.map (op (𝟙 (unop U).2.obj)) ≫ (s.ι.app U).app WalkingCospan.right = (s.ι.app U).app WalkingCospan.right by simpa
        suffices op (𝟙 (unop U).2.obj) = 𝟙 ((op U.unop.2.obj))  by
          rw [this]
          simp
        rfl
      | .one =>
        suffices  F.map (op (𝟙 ((unop U).1.obj ⊓ (unop U).2.obj))) ≫ (s.ι.app U).app WalkingCospan.one =
  (s.ι.app U).app WalkingCospan.one by simpa
        suffices op (𝟙 (((unop U).1.obj ⊓ (unop U).2.obj))) = 𝟙 ((op (((unop U).1.obj ⊓ (unop U).2.obj))))  by
          rw [this]
          simp
        rfl

  uniq s m hm := by
    ext x
    match x with
      | .left =>
        apply colimit.hom_ext
        intro U
        suffices colimit.ι (jLeft K1 K2 ⋙ F) U ≫ m.app WalkingCospan.left = F.map (op (𝟙 (unop U).1.obj)) ≫ (s.ι.app U).app WalkingCospan.left by simpa
        suffices op (𝟙 (unop U).1.obj) = 𝟙 ((op U.unop.1.obj))  by
          rw [this,  ← hm _]
          simp
        rfl
      | .right =>
        apply colimit.hom_ext
        intro U
        suffices colimit.ι (jRight K1 K2 ⋙ F) U ≫ m.app WalkingCospan.right = F.map (op (𝟙 (unop U).2.obj)) ≫ (s.ι.app U).app WalkingCospan.right by simpa
        suffices op (𝟙 (unop U).2.obj) = 𝟙 ((op U.unop.2.obj))  by
          rw [this,  ← hm _]
          simp
        rfl
      | .one =>
        apply colimit.hom_ext
        intro U
        suffices colimit.ι (jOne K1 K2 ⋙ F) U ≫ m.app WalkingCospan.one = F.map (op (𝟙 ((unop U).1.obj ⊓ (unop U).2.obj))) ≫ (s.ι.app U).app WalkingCospan.one by simpa
        suffices op (𝟙 (((unop U).1.obj ⊓ (unop U).2.obj))) = 𝟙 ((op (((unop U).1.obj ⊓ (unop U).2.obj))))  by
          rw [this, ← hm ]
          simp
        rfl

@[simps]
def truc : jCup K1 K2 ⋙ F ⟶ (FUInterWC F K1 K2).flip.obj x where
  app U := F.map (op (homOfLE ( match x with
      | .left => by simp
      | .right => by simp
      | .one => by exact inf_le_sup)))
  naturality U V f := match x with
    | _ => by
      suffices F.map _ ≫ F.map _ = F.map _ ≫ F.map _ by simpa
      rw [← F.map_comp, ← F.map_comp]
      rfl

@[simps]
def limFUInterWCFlipπ : (Functor.const WalkingCospan).obj (jCup K1 K2 ⋙ F) ⟶ (FUInterWC F K1 K2).flip where
  app x := truc F K1 K2 x
  naturality {a b} f:= match f with
    | _ => by
      ext
      suffices F.map _ = F.map _ ≫ F.map _ by simpa
      rw [← F.map_comp]
      rfl

@[simps]
def limFUInterWCFlip : Cone (FUInterWC F K1 K2 ).flip where
  pt := (jCup K1 K2) ⋙ F
  π := limFUInterWCFlipπ F K1 K2

open TopCat

variable (F : Sheaf C (of X))

variable (s : Cone (FUInterWC F.val K1 K2).flip) (U : (KsubU_cat K1 trueCond × KsubU_cat K2 trueCond)ᵒᵖ)

@[simps]
def FUInterWCConeToPullbackCone (U : (KsubU_cat K1 trueCond × KsubU_cat K2 trueCond)ᵒᵖ ) : PullbackCone (F.val.1.map (homOfLE inf_le_left : U.unop.1.obj ⊓ U.unop.2.obj ⟶ _).op) (F.val.1.map (homOfLE inf_le_right).op) where
  pt := s.pt.obj U
  π := by
    refine natTransWcspFunc _ _ ?_ ?_ ?_ ?_ ?_
    · exact (s.π.app .left).app U
    · exact (s.π.app .right).app U
    · exact (s.π.app .one).app U
    · have : s.π.app .one = s.π.app .left ≫ (FUInterWC F.val K1 K2).flip.map WalkingCospan.Hom.inl:= by
        rw [← s.π.naturality (WalkingCospan.Hom.inl)]
        simp
      rw [this]
      suffices 𝟙 (s.pt.obj U) ≫ (s.π.app .left).app U ≫ F.val.map (op (homOfLE _)) = (s.π.app .left).app U ≫ F.val.map (homOfLE _).op by dsimp; assumption
      rw [Category.id_comp]
      rfl
    · have : s.π.app .one = s.π.app .right ≫ (FUInterWC F.val K1 K2).flip.map WalkingCospan.Hom.inr:= by
        rw [← s.π.naturality (WalkingCospan.Hom.inr)]
        simp
      rw [this]
      suffices 𝟙 (s.pt.obj U) ≫ (s.π.app .right).app U ≫ F.val.map (op (homOfLE _)) = (s.π.app .right).app U ≫ F.val.map (homOfLE _).op by dsimp; assumption
      rw [Category.id_comp]
      rfl


/-def sπapx W :  (s.pt.obj W) ⟶ ((FUInterWC F.val K1 K2).obj W).obj x := match x with
  | .left => (s.π.app .left).app W
  | .right => (s.π.app .right).app W
  | .one => (s.π.app .one).app W

lemma trucbidule U : sπapx K1 K2 x F s U = ((FUInterWCConeToPullbackCone K1 K2 F s U).π.app x : (s.pt.obj U) ⟶ ((FUInterWC F.val K1 K2).obj U).obj x ) := by sorry -/

/-variable {A :WalkingCospan →  Type z} (f : WalkingCospan → A x)

lemma bidule : f x = (match x with
  | .left => f .left
  | .right => f .right
  | .one => f .one) := by
    match x with
      | .left => rfl
      | .right => rfl
      | .one => rfl-/

@[simps]
def limFUInterWCFlipLimLift : s.pt ⟶ jCup K1 K2 ⋙ F.val where
  app U := (Sheaf.isLimitPullbackCone F U.unop.1.obj U.unop.2.obj).lift (FUInterWCConeToPullbackCone K1 K2 F s U)
  naturality {U V } f := by
    let h := (Sheaf.isLimitPullbackCone F V.unop.1.obj V.unop.2.obj).uniq ((FUInterWCConeToPullbackCone K1 K2 F s V).extend (s.pt.map f))

    apply Eq.trans
    · apply h
      simp
    · apply Eq.symm
      apply h
      intro x -- try to write the proof without the case disjonction on x but too much typing issue in the statements of the intermediate steps
      -- il faudrait un lemme du genre match x with | _ => f(_) =f(x)
      --mais en léat ça ne marche pas

      /-simp
      let f := (fun x => (s.π.app x).app V)
      --#check bidule x f

      rw [← bidule x (fun x => (s.π.app x).app V)]-/

      match x with
        | .left =>
          have : (F.isLimitPullbackCone (unop U).1.obj (unop U).2.obj).lift (FUInterWCConeToPullbackCone K1 K2 F s U) ≫ (F.interUnionPullbackCone (unop U).1.obj (unop U).2.obj).fst = (s.π.app .left).app U := (Sheaf.isLimitPullbackCone F U.unop.1.obj U.unop.2.obj).fac (FUInterWCConeToPullbackCone K1 K2 F s U) .left
          suffices (F.isLimitPullbackCone (unop U).1.obj (unop U).2.obj).lift (FUInterWCConeToPullbackCone K1 K2 F s U) ≫ F.val.map (op (homOfLE _)) ≫ (F.interUnionPullbackCone (unop V).1.obj (unop V).2.obj).fst = (s.π.app .left).app U ≫ F.val.map (op f.unop.1) by simpa
          rw [←  this, Category.assoc, Sheaf.interUnionPullbackCone_fst, Sheaf.interUnionPullbackCone_fst, ← F.val.map_comp, ← F.val.map_comp ]
          rfl
        | .right =>
          have : (F.isLimitPullbackCone (unop U).1.obj (unop U).2.obj).lift (FUInterWCConeToPullbackCone K1 K2 F s U) ≫ (F.interUnionPullbackCone (unop U).1.obj (unop U).2.obj).snd = (s.π.app .right).app U := (Sheaf.isLimitPullbackCone F U.unop.1.obj U.unop.2.obj).fac (FUInterWCConeToPullbackCone K1 K2 F s U) .right

          suffices (F.isLimitPullbackCone (unop U).1.obj (unop U).2.obj).lift (FUInterWCConeToPullbackCone K1 K2 F s U) ≫ F.val.map (op (homOfLE _)) ≫ (F.interUnionPullbackCone (unop V).1.obj (unop V).2.obj).snd = (s.π.app .right).app U ≫ F.val.map (op f.unop.2) by simpa
          rw [←  this, Category.assoc, Sheaf.interUnionPullbackCone_snd, Sheaf.interUnionPullbackCone_snd, ← F.val.map_comp, ← F.val.map_comp ]
          rfl
        | .one =>
          have : (F.isLimitPullbackCone (unop U).1.obj (unop U).2.obj).lift (FUInterWCConeToPullbackCone K1 K2 F s U) ≫ (F.interUnionPullbackCone (unop U).1.obj (unop U).2.obj).fst ≫ F.val.map (homOfLE (inf_le_left : (unop U).1.obj ⊓ (unop U).2.obj ≤ (unop U).1.obj)).op = (s.π.app WalkingCospan.one).app U :=  (Sheaf.isLimitPullbackCone F U.unop.1.obj U.unop.2.obj).fac (FUInterWCConeToPullbackCone K1 K2 F s U) .one

          suffices (F.isLimitPullbackCone (unop U).1.obj (unop U).2.obj).lift (FUInterWCConeToPullbackCone K1 K2 F s U) ≫ F.val.map (op (homOfLE _)) ≫ (F.interUnionPullbackCone (unop V).1.obj (unop V).2.obj).fst ≫ F.val.map (homOfLE (inf_le_left : (unop V).1.obj ⊓ (unop V).2.obj ≤ (unop V).1.obj)).op = (s.π.app WalkingCospan.one).app U ≫ F.val.map (op (homOfLE _)) by simpa
          rw [← this, Category.assoc, Sheaf.interUnionPullbackCone_fst, Sheaf.interUnionPullbackCone_fst, ← F.val.map_comp,← F.val.map_comp, ← F.val.map_comp, ← F.val.map_comp ]
          rfl

@[simps]
def limFUInterWCFlipLim : IsLimit (limFUInterWCFlip F.val K1 K2) where
  lift s := limFUInterWCFlipLimLift K1 K2 F s
  fac s x:= by
    ext U
    suffices (F.isLimitPullbackCone (unop U).1.obj (unop U).2.obj).lift (FUInterWCConeToPullbackCone K1 K2 F s U) ≫ F.val.map (op (homOfLE _)) =  (s.π.app x).app U by simpa

    match x with
      | .left =>
        have : (F.isLimitPullbackCone (unop U).1.obj (unop U).2.obj).lift (FUInterWCConeToPullbackCone K1 K2 F s U) ≫ (F.interUnionPullbackCone (unop U).1.obj (unop U).2.obj).fst = (s.π.app .left).app U := (Sheaf.isLimitPullbackCone F U.unop.1.obj U.unop.2.obj).fac (FUInterWCConeToPullbackCone K1 K2 F s U) .left

        rw [← this, Sheaf.interUnionPullbackCone_fst]
        rfl
      | .right =>
        have : (F.isLimitPullbackCone (unop U).1.obj (unop U).2.obj).lift (FUInterWCConeToPullbackCone K1 K2 F s U) ≫ (F.interUnionPullbackCone (unop U).1.obj (unop U).2.obj).snd = (s.π.app .right).app U := (Sheaf.isLimitPullbackCone F U.unop.1.obj U.unop.2.obj).fac (FUInterWCConeToPullbackCone K1 K2 F s U) .right

        rw [← this, Sheaf.interUnionPullbackCone_snd]
        rfl
      | .one =>
        have : (F.isLimitPullbackCone (unop U).1.obj (unop U).2.obj).lift (FUInterWCConeToPullbackCone K1 K2 F s U) ≫ (F.interUnionPullbackCone (unop U).1.obj (unop U).2.obj).fst ≫ F.val.map (homOfLE (inf_le_left : (unop U).1.obj ⊓ (unop U).2.obj ≤ (unop U).1.obj)).op = (s.π.app WalkingCospan.one).app U :=  (Sheaf.isLimitPullbackCone F U.unop.1.obj U.unop.2.obj).fac (FUInterWCConeToPullbackCone K1 K2 F s U) .one

        rw [← this, Sheaf.interUnionPullbackCone_fst, ← F.val.map_comp]
        rfl
  uniq s (m : s.pt ⟶ jCup K1 K2 ⋙ F.val) hm:= by
    ext U
    apply (F.isLimitPullbackCone (unop U).1.obj (unop U).2.obj).uniq (FUInterWCConeToPullbackCone K1 K2 F s U)
    intro x
    match x with
      | .left =>
        suffices m.app U ≫ (F.interUnionPullbackCone (unop U).1.obj (unop U).2.obj).fst = (s.π.app WalkingCospan.left).app U by simpa
        rw [Sheaf.interUnionPullbackCone_fst, ← hm]
        rfl
      | .right =>
        suffices m.app U ≫ (F.interUnionPullbackCone (unop U).1.obj (unop U).2.obj).snd = (s.π.app WalkingCospan.right).app U by simpa
        rw [Sheaf.interUnionPullbackCone_snd, ← hm]
        rfl
      | .one =>
        suffices m.app U ≫ (F.interUnionPullbackCone (unop U).1.obj (unop U).2.obj).fst ≫ F.val.map (homOfLE _).op =
  (s.π.app WalkingCospan.one).app U by simpa
        rw [Sheaf.interUnionPullbackCone_fst, ← hm, ← F.val.map_comp]
        rfl

@[simps!]
def colimFUCapπ : (Functor.const WalkingCospan).obj (colimit (jCup K1 K2 ⋙ F.val)) ⟶ (colimFUInterWC F.val K1 K2).pt := by
  refine natTransWcspFunc _ _ ?_ ?_ ?_ ?_ ?_
  · exact colimMap (whiskerRight (jCToJL K1 K2) F.val)
  · exact colimMap (whiskerRight (jCToJR K1 K2) F.val)
  · exact colimMap (whiskerRight (jCToJR K1 K2 ≫ jRToJO K1 K2) F.val) -- C → R → O = C → L → 0
  · apply colimit.hom_ext
    intro U
    suffices F.val.map ((jCToJR K1 K2).app U) ≫ F.val.map ((jRToJO K1 K2).app U) ≫ colimit.ι (jOne K1 K2 ⋙ F.val) U = F.val.map ((jCToJL K1 K2).app U) ≫ F.val.map ((jLToJO K1 K2).app U) ≫ colimit.ι (jOne K1 K2 ⋙ F.val) U by simpa
    rw [ ← Category.assoc, ← Category.assoc, ← F.val.map_comp, ← F.val.map_comp]
    rfl
  · apply colimit.hom_ext
    intro U
    simp

@[simps]
def limColimFUCap : Cone ((colimFUInterWC F.val K1 K2 ).pt) where
  pt := colimit (jCup K1 K2 ⋙ F.val)
  π := colimFUCapπ K1 K2 F

variable (s : Cone (colimFUInterWC F.val K1 K2).pt)

#check colimit.desc

def limColimFUCapIsLim : IsLimit (limColimFUCap K1 K2 F ) where
  lift s := by
    simp
    let h := s.π.app .one -- du coup pas sur du truc plus haut
    dsimp at h

    apply h ≫ _
    refine colimMap ?_
    refine (whiskerRight ?_ F.val)
    exact ⟨ fun U => by
      apply op
      apply homOfLE
      simp
      sorry,sorry ⟩
  fac := sorry
  uniq := sorry

@[simps]
def colimLimFUInterWCFlipι :jCup K1 K2 ⋙ F.val ⟶ (Functor.const (KsubU_cat K1 trueCond × KsubU_cat K2 trueCond)ᵒᵖ).obj (colimit (jCup K1 K2 ⋙ F.val)) where
  app U := colimit.ι (jCup K1 K2 ⋙ F.val) U
  naturality {U V} f := by
    rw [colimit.w]
    simp

def colimLimFUInterWCFlip : Cocone ((limFUInterWCFlip F.val K1 K2).pt) := colimit.cocone (limFUInterWCFlip F.val K1 K2).pt

def colimLimFUInterWCFlipIsColim : IsColimit (colimLimFUInterWCFlip K1 K2 F) := colimit.isColimit (limFUInterWCFlip F.val K1 K2).pt
