import Mathlib
import M2.KsubU
import M2.RCalpha

open CategoryTheory Limits TopologicalSpace Compacts Opposite Functor TopCat

universe u1 u2 u3 u4 v1 v2 v3 v4

section
variable {A : Type u1} [Category.{v1, u1} A] {B : Type u3} [Category.{v3, u3} B]
variable (F : A ⥤ Cat.{v2, u2})

@[simps!]
def GIdIso (F : A ⥤ Cat.{v2, u2}) (G : (a : A) → (F.obj a) ⥤ B) (a : A) : (F.map (𝟙 _) ⋙ (G a) ≅ (G a)) := eqToIso (by
  apply CategoryTheory.Functor.ext
  intro b c f
  apply eq_of_heq
  apply (heq_eqToHom_comp_iff _ _ _).2
  apply (heq_comp_eqToHom_iff _ _ _).2
  congr
  · simp [F.map_id]
    rfl
  · simp)

@[simps!]
def FmapCompGIso (F : A ⥤ Cat.{v2, u2}) (G : (a : A) → (F.obj a) ⥤ B) (iso : { a b : A} → (f : a ⟶ b) → (F.map f) ⋙ G b ≅ G a) {a b c : A } (f : a ⟶ b) (g :b ⟶ c) : F.map (f ≫ g) ⋙ G c ≅ G a := isoWhiskerRight (eqToIso (F.map_comp _ _)) (G c) ≪≫ associator (F.map f) (F.map g) (G c) ≪≫ isoWhiskerLeft (F.map f) (iso g) ≪≫ iso f

variable (B : Type u3) [Category.{v3, u3} B]
structure CoconeFunctor (F : A ⥤ Cat.{v2, u2}) where
-- B n'est pas dans la structure pour eviter des soucis d'inference de type par la suite
  i : (x : A) → (F.obj x) ⥤ B
  iso : { x y : A} → (f : x ⟶ y) → (F.map f) ⋙ i y ≅ i x
  isoId : (x  : A) → (iso (𝟙 x)) = GIdIso F i x
  isoComp : {x y z: A } → (f : x ⟶ y) → (g : y ⟶ z) → (iso (f ≫ g) = FmapCompGIso F i iso f g)

/-structure IsColimitF (t : CoconeFunctor B F) where
  desc : {C : Cat.{v4, u4}} → (s : CoconeFunctor C F) → B ⥤ C
  fac : {C : Cat.{v4, u4}} → (s : CoconeFunctor C F) → (a : A) → (t.i a) ⋙ desc s = (s.i a)--probablement à transformer en iso plus tard
  uniq : {C : Cat.{v4, u4}} → (s : CoconeFunctor C F) → (m : B ⥤ C) → (∀ (a : A), (t.i a) ⋙ m = (s.i a)) → m = desc s-/

variable {B : Type u3} [Category.{v3, u3} B] {C : Type u4} [Category.{v4, u4} C]

@[simps]
def  CoconeFWhisker (s : CoconeFunctor B F) (H : B ⥤ C) : CoconeFunctor C F where
i x := s.i x ⋙ H
iso f := (associator (F.map f) (s.i _) H) ≪≫ (isoWhiskerRight (s.iso f) H)
isoId a := by
  ext
  suffices H.map (eqToHom _ ) = eqToHom _ by simpa [s.isoId ]
  apply eqToHom_map
isoComp f g := by
  ext
  simp [s.isoComp]

end

section

variable {A : Type u1} [Category.{v1, u1} A] {C : Type u2} [Category.{v2, u2} C] {D : Type u3} [Category.{v3, u3} D]

variable {i : A ⥤ Cat.{v4, u4}} (iaSubC : CoconeFunctor C i) (FcupIa : C ⥤ D) (a : A)

def F : CoconeFunctor D i := CoconeFWhisker i iaSubC FcupIa

--variable (h : IsColimitF i C iaSubC)

/-lemma bidule : FcupIa = @h.desc _ _ (Cat.of D) (F iaSubC FcupIa)  := by
  apply @h.uniq  _ _ (Cat.of D) (F iaSubC FcupIa)
  intro a
  simp [F]-/

variable (a : A)

variable [(a : A) → HasLimitsOfSize.{v3, u3} (i.obj a)]

noncomputable section

variable [HasLimitsOfSize.{v2, u2} D] [HasLimitsOfSize.{v4, u4} D]

#check limit (FcupIa )

-- pas sur du op mais ça à l'air de marcher mieux
@[simps]
def limFia : Aᵒᵖ ⥤ D where
  obj a := limit ((F iaSubC FcupIa).i a.unop)
  map f := (limit.pre ((F iaSubC FcupIa).i _) (i.map f.unop)) ≫ ((HasLimit.isoOfNatIso ((F iaSubC FcupIa).iso f.unop)).hom )
  map_id a := by
    ext
    rw [unop_id, Category.assoc, HasLimit.isoOfNatIso_hom_π, (F iaSubC FcupIa).isoId]
    simp
  map_comp f g := by
    ext
    suffices limit.π _ _ ≫ _ = limit.π _ _ ≫ _ by simpa
    rw [(F iaSubC FcupIa).isoComp]
    simp

variable [HasLimitsOfSize.{v1, u1} D]

#check limit (limFia iaSubC FcupIa )

structure repObj (x : C) where
  a : A
  ia : i.obj a
  rep : (iaSubC.i a).obj ia ≅ x

structure repHom {x y : C} (f : x ⟶ y) where
  a : A
  iaDom : i.obj a
  iaCoDom : i.obj a
  repDom : (iaSubC.i a).obj iaDom ≅ x
  repCoDom : (iaSubC.i a).obj iaCoDom ≅ y
  hom : iaDom ⟶ iaCoDom
  rep : repDom.inv ≫(iaSubC.i a).map hom ≫ repCoDom.hom =  f

structure lifting {x : C} (r s : repObj iaSubC x) where
  hom : r.a ⟶ s.a
  liftIso : (i.map hom).obj r.ia ≅ s.ia
  compat : r.rep.hom ≫ s.rep.inv = ((iaSubC.iso hom).inv).app r.ia ≫ (iaSubC.i s.a).map liftIso.hom

variable (repO : (x : C) → repObj iaSubC x)
variable (repH : {x y : C} → ( f: x ⟶ y) → repHom iaSubC f)
--def repAHom (x y : C) : A := repA<| IsFiltered.max x y


@[simps]
def repHtoD {x y : C} (f : x ⟶ y) (r : repHom iaSubC f) : (repObj iaSubC x) := ⟨r.a,r.iaDom,r.repDom⟩

@[simps]
def repHtoCd {x y : C} (f : x ⟶ y) (r : repHom iaSubC f) : (repObj iaSubC y) := ⟨r.a,r.iaCoDom,r.repCoDom⟩

@[simps]
def repCanO (a : A) (x : i.obj a) : repObj iaSubC ((iaSubC.i a).obj x) where
  a := a
  ia := x
  rep := eqToIso rfl

/- If the representation r is a lifting of the representation s then the morphism limit.π _ ≫ limit.π _ is the same for r and s -/
omit [∀ (a : A), HasLimitsOfSize.{v3, u3, v4, u4} ↑(i.obj a)] [HasLimitsOfSize.{v2, u2, v3, u3} D] in
lemma limLimIndepOfLift {x : C}  (r s : repObj iaSubC x) (l : lifting iaSubC r s) : limit.π (limFia iaSubC FcupIa ) (op r.a) ≫ limit.π ((F iaSubC FcupIa).i r.a) r.ia ≫ FcupIa.map r.rep.hom = limit.π (limFia iaSubC FcupIa ) (op s.a) ≫ limit.π ((F iaSubC FcupIa).i s.a) s.ia ≫ FcupIa.map s.rep.hom := by

  rw [← limit.w (limFia iaSubC FcupIa) l.hom.op, Category.assoc]
  apply whisker_eq

  have : r.rep.hom = ((iaSubC.iso l.hom).inv).app r.ia ≫ (iaSubC.i s.a).map l.liftIso.hom ≫ s.rep.hom := by
    rw [← Category.assoc, ← l.compat]
    simp

  rw [this, ← limit.w ((F iaSubC FcupIa).i s.a) l.liftIso.hom ]

  suffices limit.π (iaSubC.i s.a ⋙ FcupIa) ((i.map l.hom).obj r.ia) ≫ _ = limit.π (iaSubC.i s.a ⋙ FcupIa) ((i.map l.hom).obj r.ia) ≫ _ by simpa [F]
  -- ici suffices _ =_ by simp[F] suffit

  apply whisker_eq

  suffices (iaSubC.iso l.hom).hom.app r.ia ≫  (iaSubC.iso l.hom).inv.app r.ia ≫ (iaSubC.i s.a).map l.liftIso.hom = (iaSubC.i s.a).map l.liftIso.hom  by
    rw [← Category.assoc, ← Category.assoc]
    apply eq_whisker
    rw [← FcupIa.map_comp, ← FcupIa.map_comp, Category.assoc, this]
  simp

variable (repLifting : {x : C} → (r s : repObj iaSubC x) → (t : repObj iaSubC x) × (lifting iaSubC r t) × (lifting iaSubC s t))


include repLifting
omit [∀ (a : A), HasLimitsOfSize.{v3, u3, v4, u4} ↑(i.obj a)] [HasLimitsOfSize.{v2, u2, v3, u3} D] in
@[simp]
theorem limLimIndep {x : C}  (r s : repObj iaSubC x) : limit.π (limFia iaSubC FcupIa ) (op r.a) ≫ limit.π ((F iaSubC FcupIa).i r.a) r.ia ≫ FcupIa.map r.rep.hom = limit.π (limFia iaSubC FcupIa ) (op s.a) ≫ limit.π ((F iaSubC FcupIa).i s.a) s.ia ≫ FcupIa.map s.rep.hom := Eq.trans (limLimIndepOfLift iaSubC FcupIa r (repLifting r s).fst (repLifting r s).snd.1)
      (Eq.symm (limLimIndepOfLift iaSubC FcupIa s (repLifting r s).fst (repLifting r s).snd.2))


/-- The natural transformation involved in limLimFIaConeFcupIa-/
@[simps]
def limLimFiaConeFcupIaπ : (const C).obj (limit (limFia iaSubC FcupIa)) ⟶ FcupIa where
  app x := by
    let xr := repO x

    exact limit.π (limFia iaSubC FcupIa ) (op xr.a) ≫ limit.π ((F iaSubC FcupIa).i xr.a) xr.ia ≫ FcupIa.map xr.rep.hom

    --limit.π (limFia h3) (op (repA x)) ≫ limit.π (Fia (repA x)) (repIa x) ≫ (FiaFacIso h1 (repA x)).inv.app _ ≫ FcupIa.map (repSpec x).hom
  naturality x y f:= by
    let fr := repH f

    rw [limLimIndep iaSubC FcupIa repLifting (repO y) (repHtoCd iaSubC f fr)]
    rw [limLimIndep iaSubC FcupIa repLifting (repO x) (repHtoD iaSubC f fr)]

    suffices limit.π (limFia iaSubC FcupIa) (op fr.a) ≫ limit.π ((F iaSubC FcupIa).i fr.a) fr.iaCoDom ≫ FcupIa.map fr.repCoDom.hom = limit.π (limFia iaSubC FcupIa) (op fr.a) ≫ limit.π ((F iaSubC FcupIa).i fr.a) fr.iaDom ≫ FcupIa.map fr.repDom.hom ≫ FcupIa.map f by simpa

    apply whisker_eq
    rw [← limit.w ((F iaSubC FcupIa).i fr.a) fr.hom]
    rw [Category.assoc]

    apply whisker_eq
    suffices FcupIa.map ((iaSubC.i fr.a).map fr.hom) ≫ FcupIa.map fr.repCoDom.hom = FcupIa.map fr.repDom.hom ≫ FcupIa.map f by simpa [F]
    repeat rw [← FcupIa.map_comp]
    apply congr_arg
    calc (iaSubC.i fr.a).map fr.hom ≫ fr.repCoDom.hom = fr.repDom.hom ≫ fr.repDom.inv ≫ (iaSubC.i fr.a).map fr.hom ≫ fr.repCoDom.hom := by simp
      _ = fr.repDom.hom ≫ (fr.repDom.inv ≫ (iaSubC.i fr.a).map fr.hom ≫ fr.repCoDom.hom) := by simp
      _ = fr.repDom.hom ≫ f := by rw [fr.rep]


/-- The structure of cone over FCupIa on the limit of limit of FIa's-/
@[simps!]
def limLimFiaConeFcupIa : Cone FcupIa where
  pt := limit (limFia iaSubC FcupIa )
  π := limLimFiaConeFcupIaπ iaSubC FcupIa repO repH repLifting

/--The natural transformation involved in fCupIaConeToFiaCone-/
@[simps]
def fCupIaConeToFiaConeπ (s : Cone FcupIa) : (const (i.obj a)).obj s.pt ⟶ (F iaSubC FcupIa).i a where
  app x := s.π.app ((iaSubC.i a).obj x)
  naturality x1 x2 f:= by
    simp [F]

/-- The cone structure  over Fia of a cone over FcupIa-/
@[simps]
def fCupIaConeToFiaCone (s : Cone FcupIa) : Cone ((F iaSubC FcupIa).i a) where
  pt := s.pt
  π := fCupIaConeToFiaConeπ iaSubC FcupIa a s

/--The natural transformation involved in fCupIaConeToLimFiaCone-/
@[simps]
def fCupIaConeToLimFiaConeπ (s : Cone FcupIa) : (const Aᵒᵖ).obj s.pt ⟶ limFia iaSubC FcupIa where
  app a := limit.lift _ (fCupIaConeToFiaCone iaSubC FcupIa a.unop s)
  naturality a b f:= by
    apply limit.hom_ext
    intro j
    simp [F]

/-- The cone structure  over lim FIa of a cone over FcupIa-/
@[simps]
def fCupIaConeToLimFiaCone (s : Cone FcupIa ) : Cone (limFia iaSubC FcupIa) where
  pt := s.pt
  π := fCupIaConeToLimFiaConeπ iaSubC FcupIa s


/-- The evidence that the limit of limit is a limit -/
@[simps]
def limLimIsLim : IsLimit (limLimFiaConeFcupIa iaSubC FcupIa repO repH repLifting) where
  lift s := limit.lift _ (fCupIaConeToLimFiaCone iaSubC FcupIa s)
  uniq s (m : s.pt ⟶ limit (limFia iaSubC FcupIa)) hm:= by
    apply limit.hom_ext
    intro a
    apply limit.hom_ext
    intro x
    suffices m ≫ limit.π (limFia iaSubC FcupIa) a ≫ limit.π ((F iaSubC FcupIa).i (unop a)) x = s.π.app ((iaSubC.i (unop a)).obj x) by simpa

    rw [← hm _]

    apply whisker_eq
    have : limit.π (limFia iaSubC FcupIa) a ≫ limit.π ((F iaSubC FcupIa).i (unop a)) x = limit.π (limFia iaSubC FcupIa ) (op (repCanO iaSubC (unop a) x).a) ≫ limit.π ((F iaSubC FcupIa).i (repCanO iaSubC (unop a) x).a) (repCanO iaSubC (unop a) x).ia ≫ FcupIa.map (repCanO iaSubC (unop a) x).rep.hom := by simp [F]

    rw [this, limLimIndep iaSubC FcupIa repLifting (repCanO iaSubC a.unop x) (repO ((iaSubC.i (unop a)).obj x))]

    apply whisker_eq
    simp [F]


end

noncomputable section -- pour avoir au moins une situation ou ce qui précède s'applique

variable {X : Type u1} [TopologicalSpace X] [T2Space X] (K : Compacts X)
variable {D : Type u2} [Category.{u2, u2} D] (F : (Opens X)ᵒᵖ ⥤ D)

@[simps]
def iEx : (supSupK_cat K)ᵒᵖ  ⥤ Cat where
  obj L := Cat.of (KsubU_cat L.unop.obj trueCond)ᵒᵖ
  map f := Functor.op (K1subK2subU _ ((fullSubcategoryInclusion _ ).map f.unop))

#check iEx

@[simps]
def iaSubCExi (L : (supSupK_cat K)ᵒᵖ ) : ((iEx K ).obj L) ⥤ (KsubU_cat K trueCond)ᵒᵖ  where
  obj U := ⟨U.unop.obj,⟨Set.Subset.trans (supSupKtoSupK K (unop L)) (unop U).property.left, of_eq_true (eq_self true)⟩⟩
  map f := op <| homOfLE <| leOfHom f.unop

@[simps]
def iaSubCEx : CoconeFunctor (KsubU_cat K trueCond)ᵒᵖ (iEx K) where
  i := iaSubCExi K
  iso _ := eqToIso rfl
  isoId _ := rfl
  isoComp _ _ := rfl

def FcupIaEx  : (KsubU_cat K trueCond)ᵒᵖ ⥤ D := (fullSubcategoryInclusion _ ).op ⋙ F

#check CoconeFWhisker _ (iaSubCEx K) (FcupIaEx K F)

variable [HasLimitsOfSize.{u1, u1, u2, u2} D]

#check limFia (iaSubCEx K) (FcupIaEx K F)

variable [LocallyCompactSpace X]

variable (repCompat : (x : C) → (r1 r2 : repObj iaSubC x) → ∃ g : r1.a ⟶ r2.a, (i.map g).obj r1.ia = r2.ia ∨ ∃ g : r2.a ⟶ r1.a, (i.map g).obj r2.ia = r1.ia )


@[simps]
def repOEx (U : (KsubU_cat K trueCond)ᵒᵖ) : (repObj (iaSubCEx K) U ) where
  a := by
    let ⟨L,hL⟩ := Classical.choice (existsIntermed X K U.unop.obj U.unop.property.1)
    apply op
    use ⟨L, hL.1⟩
    use ⟨interior L,@isOpen_interior X L _⟩
    constructor
    exact hL.2.1
    exact interior_subset
  ia := op ⟨U.unop.obj, by
      constructor
      exact (Classical.choice (existsIntermed X K U.unop.obj U.unop.property.1)).2.2.2
      rfl⟩
  rep := eqToIso rfl

@[simps]
def repHEx {U V : (KsubU_cat K trueCond)ᵒᵖ} (f : U ⟶ V) : repHom (iaSubCEx K) f where
  a := (repOEx K V).a
  iaDom := ⟨U.unop.obj, by
    constructor
    apply Set.Subset.trans _ (leOfHom f.unop)
    exact (Classical.choice (existsIntermed X K V.unop.obj V.unop.property.1)).2.2.2
    simp⟩
  iaCoDom := (repOEx K V).ia
  repDom := Iso.refl _
  repCoDom := (repOEx K V).rep
  hom := op <| homOfLE ( leOfHom f.unop)
  rep := rfl

omit [LocallyCompactSpace X] in
lemma iaExEqU {U : (KsubU_cat K trueCond)ᵒᵖ} (r : repObj (iaSubCEx K) U) : (unop r.ia).obj = (unop U).obj := antisymm (leOfHom (r.rep.inv.unop)) (leOfHom (r.rep.hom.unop))

@[simps]
def resupEx {U : (KsubU_cat K trueCond)ᵒᵖ}  (r s : repObj (iaSubCEx K) U) : (repObj (iaSubCEx K) U) where
  a := op <| InfSupSupK K r.a.unop s.a.unop
  ia := ⟨r.ia.unop.obj ⊓ s.ia.unop.obj, by
    constructor
    · apply Set.subset_inter_iff.2
      constructor
      · apply Set.Subset.trans
        apply leOfHom (InfInLeftSSK K (unop r.a) (unop s.a))
        exact r.ia.unop.property.1
      · apply Set.Subset.trans
        apply leOfHom (InfInRightSSK K (unop r.a) (unop s.a))
        exact s.ia.unop.property.1
    · rfl⟩
  rep := by
    apply eqToIso
    apply (Opposite.unop_inj_iff _ _).1
    apply FullSubcategory.ext
    simp_all only [iaSubCEx, iaSubCExi, iaExEqU K r, iaExEqU K s, le_refl, inf_of_le_left]

@[simps]
def liftingToSupLeft {U : (KsubU_cat K trueCond)ᵒᵖ}  (r s : repObj (iaSubCEx K) U) : lifting (iaSubCEx K) r (resupEx K r s) where
  hom := op <| InfInLeftSSK K (unop r.a) (unop s.a)
  liftIso := by
    apply eqToIso
    simp [K1subK2subU]
    apply FullSubcategory.ext
    simp [iaExEqU K r, iaExEqU K s]
  compat := by
    simp only [iaSubCEx, iaSubCExi]
    rfl

@[simps]
def liftingToSupRight {U : (KsubU_cat K trueCond)ᵒᵖ}  (r s : repObj (iaSubCEx K) U) : lifting (iaSubCEx K) s (resupEx K r s) where
  hom := op <| InfInRightSSK K (unop r.a) (unop s.a)
  liftIso := by
    apply eqToIso
    simp [K1subK2subU]
    apply FullSubcategory.ext
    simp [iaExEqU K r, iaExEqU K s]
  compat := by
    simp only [iaSubCEx, iaSubCExi]
    rfl

def repLiftingEx {U : (KsubU_cat K trueCond)ᵒᵖ}  (r s : repObj (iaSubCEx K) U) : (t : repObj (iaSubCEx K) U) × (lifting (iaSubCEx K) r t) × (lifting (iaSubCEx K) s t) := by
  use resupEx K r s
  constructor
  · apply liftingToSupLeft
  · apply liftingToSupRight


#check limLimIsLim (iaSubCEx K) (FcupIaEx K F) (repOEx K) (repHEx K) (repLiftingEx K)

--#lint

/-@[simps]
def truc4 {U V : (KsubU_cat K trueCond)} (f : U ⟶ V) : ((KsubU_cat (repAEx K ( op U)).unop.obj trueCond) ) where
  obj := V.obj
  property := by
    constructor
    apply Set.Subset.trans _ (leOfHom f)
    exact (Classical.choice (existsIntermed X K U.obj U.property.1)).2.2.2
    simp

@[simp]
lemma truc4id (U : (KsubU_cat K trueCond)) : truc4 K (𝟙 U) = (repIaEx K (op U)).unop := rfl


lemma truc5 (U : (KsubU_cat K trueCond)) : (op (InfInLeftSSK K (unop (repAEx K (op U))) (unop (repAEx K (op U))))) = sorry := by sorry

@[simps]
def chose3 {C: Cat.{u1, u1}} (s: CoconeFunctor C (iEx K)) : (KsubU_cat K trueCond)ᵒᵖ ⥤ C where
  obj U := (s.i (repAEx K U)).obj (repIaEx K U)
  map {U V} f:= (s.iso (op ( InfInLeftSSK K (repAEx K U).unop (repAEx K V).unop))).inv.app (repIaEx K U) ≫ ((s.i _).map <| op <| 𝟙 _) ≫ (s.iso (op ( InfInRightSSK K (repAEx K U).unop (repAEx K V).unop))).hom.app (op (truc4 K f.unop)) ≫ (s.i (repAEx K _ )).map (op <| homOfLE<| leOfHom f.unop)/-by
    let g1 := op ( InfInLeftSSK K (repAEx K U).unop (repAEx K V).unop)
    let g2 := op ( InfInRightSSK K (repAEx K U).unop (repAEx K V).unop)
    exact (s.iso g1).inv.app (repIaEx K U) ≫ ((s.i _).map <| op <| 𝟙 _) ≫ (s.iso g2).hom.app (op (truc4 K f.unop)) ≫ (s.i (repAEx K _ )).map (op <| homOfLE<| leOfHom f.unop)-/
  map_id U := by
    simp
    #check s.isoId
    sorry
  map_comp f g := by
    simp
    sorry

@[simps]
def chose2 : IsColimitF (iEx K) (KsubU_cat K trueCond)ᵒᵖ (chose K) where
  desc s := chose3 K s
  fac s L:= by
    apply CategoryTheory.Functor.ext
    intro U V f
    apply Functor.congr_hom
    /-· sorry --apply Functor.congr_hom
    · simp; sorry-/
  uniq s m hm := by
    apply CategoryTheory.Functor.ext
    intro U V f
    apply Functor.congr_hom



    --sorry

    --apply CategoryTheory.Functor.ext
    --simp
    --intro U V f
    --· apply Functor.congr_hom _ f


          --sorry --apply Functor.congr_hom


#check chose2-/
