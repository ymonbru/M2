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
  intros _ _ _
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

structure IsColimitF (t : CoconeFunctor B F) where
  desc : {C : Cat.{v4, u4}} → (s : CoconeFunctor C F) → B ⥤ C
  fac : {C : Cat.{v4, u4}} → (s : CoconeFunctor C F) → (a : A) → (t.i a) ⋙ desc s = (s.i a)--probablement à transformer en iso plus tard
  uniq : {C : Cat.{v4, u4}} → (s : CoconeFunctor C F) → (m : B ⥤ C) → (∀ (a : A), (t.i a) ⋙ m = (s.i a)) → m = desc s

variable {B : Type u3} [Category.{v3, u3} B] {C : Type u4} [Category.{v4, u4} C]

@[simps]
def  CoconeFWhisker (s : CoconeFunctor B F) (H : B ⥤ C) : CoconeFunctor C F where
i x := s.i x ⋙ H
iso f := (F.map f).associator  (s.i _) H ≪≫ (isoWhiskerRight (s.iso f) H)
isoId _ := by
  ext
  suffices H.map (eqToHom _ ) = eqToHom _ by simpa [s.isoId ]
  apply eqToHom_map
isoComp _ _ := by
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

--variable [(a : A) → HasLimitsOfSize.{v3, u3} (i.obj a)]

noncomputable section

variable [HasColimitsOfSize.{v2, u2} D] [HasColimitsOfSize.{v4, u4} D]

#check colimit (FcupIa )


#check ((F iaSubC FcupIa).i a)
-- pas sur du op mais ça à l'air de marcher mieux
@[simps]
def colimFia : A ⥤ D where
  obj a := colimit ((F iaSubC FcupIa).i a)
  map f := (HasColimit.isoOfNatIso ((F iaSubC FcupIa).iso f).symm).hom ≫
        colimit.pre ((F iaSubC FcupIa).i _) (i.map f)
  map_id a := by
    ext
    simp [ (F iaSubC FcupIa).isoId, colimit.eqToHom_comp_ι, i.map_id]
  map_comp f g := by
    ext
    simp [(F iaSubC FcupIa).isoComp]

variable [HasColimitsOfSize.{v1, u1} D]

#check colimit (colimFia iaSubC FcupIa )

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

variable (x : C) (r: repObj iaSubC x)

/- If the representation r is a lifting of the representation s then the morphism limit.π _ ≫ limit.π _ is the same for r and s -/
omit [HasColimitsOfSize.{v2, u2, v3, u3} D] in
lemma colimColimIndepOfLift {x : C}  (r s : repObj iaSubC x) (l : lifting iaSubC r s) : FcupIa.map r.rep.inv ≫ colimit.ι ((F iaSubC FcupIa).i r.a) r.ia ≫ colimit.ι (colimFia iaSubC FcupIa ) r.a = FcupIa.map s.rep.inv ≫ colimit.ι ((F iaSubC FcupIa).i s.a) s.ia ≫ colimit.ι (colimFia iaSubC FcupIa ) s.a := by
  rw [← colimit.w (colimFia iaSubC FcupIa) l.hom]
  repeat rw [← Category.assoc]
  apply eq_whisker
  have : s.rep.inv = r.rep.inv ≫ ((iaSubC.iso l.hom).inv).app r.ia ≫ (iaSubC.i s.a).map l.liftIso.hom := by
    rw [ ← l.compat]
    simp

  rw [this]
  simp [colimit.w ((F iaSubC FcupIa).i s.a) l.liftIso.inv, F]

  apply whisker_eq
  apply whisker_eq
  apply Eq.symm
  exact colimit.w (iaSubC.i s.a ⋙ FcupIa) l.liftIso.hom

variable (repLifting : {x : C} → (r s : repObj iaSubC x) → (t : repObj iaSubC x) × (lifting iaSubC r t) × (lifting iaSubC s t))


include repLifting
omit [HasColimitsOfSize.{v2, u2, v3, u3} D] in
@[simp]
theorem colimColimIndep {x : C}  (r s : repObj iaSubC x) : FcupIa.map r.rep.inv ≫ colimit.ι ((F iaSubC FcupIa).i r.a) r.ia ≫ colimit.ι (colimFia iaSubC FcupIa ) r.a = FcupIa.map s.rep.inv ≫ colimit.ι ((F iaSubC FcupIa).i s.a) s.ia ≫ colimit.ι (colimFia iaSubC FcupIa ) s.a := Eq.trans (colimColimIndepOfLift iaSubC FcupIa r (repLifting r s).fst (repLifting r s).snd.1)
      (Eq.symm (colimColimIndepOfLift iaSubC FcupIa s (repLifting r s).fst (repLifting r s).snd.2))


/-- The natural transformation involved in limLimFIaConeFcupIa-/
@[simps]
def colimColimFiaCoconeFcupIaι : FcupIa ⟶ (const C).obj (colimit (colimFia iaSubC FcupIa)) where
  app x := let xr := repO x; FcupIa.map xr.rep.inv ≫ colimit.ι ((F iaSubC FcupIa).i xr.a) xr.ia ≫ colimit.ι (colimFia iaSubC FcupIa ) xr.a
  naturality x y f:= by
    let fr := repH f

    rw [colimColimIndep iaSubC FcupIa repLifting (repO y) (repHtoCd iaSubC f fr)]
    rw [colimColimIndep iaSubC FcupIa repLifting (repO x) (repHtoD iaSubC f fr)]

    suffices ((FcupIa.map f ≫ FcupIa.map fr.repCoDom.inv) ≫
    colimit.ι ((F iaSubC FcupIa).i fr.a) fr.iaCoDom) ≫ colimit.ι (colimFia iaSubC FcupIa) fr.a = (FcupIa.map fr.repDom.inv ≫ colimit.ι ((F iaSubC FcupIa).i fr.a) fr.iaDom) ≫ colimit.ι (colimFia iaSubC FcupIa) fr.a by simpa

    apply eq_whisker
    rw [← colimit.w ((F iaSubC FcupIa).i fr.a) fr.hom]
    rw [← Category.assoc]

    apply eq_whisker

    suffices FcupIa.map (f ≫ fr.repCoDom.inv) = FcupIa.map (fr.repDom.inv ≫ ((iaSubC.i fr.a).map fr.hom)) by simpa [F]

    apply congr_arg

    slice_lhs 1 1 => rw [← fr.rep]
    simp


/-- The structure of cone over FCupIa on the limit of limit of FIa's-/
@[simps!]
def colimColimFiaCoconeFcupIa : Cocone FcupIa where
  pt := colimit (colimFia iaSubC FcupIa )
  ι := colimColimFiaCoconeFcupIaι iaSubC FcupIa repO repH repLifting

/--The natural transformation involved in fCupIaConeToFiaCone-/
@[simps]
def fCupIaCoconeToFiaCoconeι (s : Cocone FcupIa) : (F iaSubC FcupIa).i a ⟶ (const (i.obj a)).obj s.pt where
  app x := s.ι.app ((iaSubC.i a).obj x)
  naturality x1 x2 f:= by
    simp [F]

/-- The cone structure  over Fia of a cone over FcupIa-/
@[simps]
def fCupIaCoconeToFiaCocone (s : Cocone FcupIa) : Cocone ((F iaSubC FcupIa).i a) where
  pt := s.pt
  ι := fCupIaCoconeToFiaCoconeι iaSubC FcupIa a s

/--The natural transformation involved in fCupIaConeToLimFiaCone-/
@[simps]
def fCupIaCoconeToColimFiaCoconeι (s : Cocone FcupIa) : colimFia iaSubC FcupIa ⟶ (const A).obj s.pt where
  app a := colimit.desc _ (fCupIaCoconeToFiaCocone iaSubC FcupIa a s)
  naturality a b f:= by
    apply colimit.hom_ext
    intro j
    simp [F]

/-- The cone structure  over lim FIa of a cone over FcupIa-/
@[simps]
def fCupIaCoconeToColimFiaCocone (s : Cocone FcupIa ) : Cocone (colimFia iaSubC FcupIa) where
  pt := s.pt
  ι := fCupIaCoconeToColimFiaCoconeι iaSubC FcupIa s


/-- The evidence that the limit of limit is a limit -/
@[simps]
def colimColimIsColim : IsColimit (colimColimFiaCoconeFcupIa iaSubC FcupIa repO repH repLifting) where
  desc s := colimit.desc _ (fCupIaCoconeToColimFiaCocone iaSubC FcupIa s)
  uniq s (m : colimit (colimFia iaSubC FcupIa) ⟶ s.pt) hm:= by
    apply colimit.hom_ext
    intro a
    apply colimit.hom_ext
    intro x
    suffices colimit.ι ((F iaSubC FcupIa).i a) x ≫ colimit.ι (colimFia iaSubC FcupIa) a ≫ m = s.ι.app ((iaSubC.i a).obj x) by simpa

    rw [← hm _]

    repeat rw [← Category.assoc]
    apply eq_whisker

    suffices colimit.ι ((F iaSubC FcupIa).i a) x ≫ colimit.ι (colimFia iaSubC FcupIa) a = FcupIa.map (repO ((iaSubC.i a).obj x)).rep.inv ≫ colimit.ι ((F iaSubC FcupIa).i (repO ((iaSubC.i a).obj x)).a) (repO ((iaSubC.i a).obj x)).ia ≫ colimit.ι (colimFia iaSubC FcupIa) (repO ((iaSubC.i a).obj x)).a by simpa

    rw [ ← colimColimIndep iaSubC FcupIa repLifting (repCanO iaSubC a x) (repO ((iaSubC.i a).obj x))]

    simp [F]



--test pour voir si C peut être une colimite

#check IsColimitF i _ iaSubC

variable [IsFiltered A]

def trucDesc {B : Cat} (F: CoconeFunctor B i) : C ⥤ B where
  obj x := let xr := repO x;
      (F.i xr.a).obj xr.ia
  map {x y} f := by
    simp
    let fr := repH f
    let ⟨tx, hrotx, hrhtx⟩ := repLifting (repO x) (repHtoD iaSubC f fr)
    let ⟨ty, hroty, hrhty⟩ := repLifting (repO y) (repHtoCd iaSubC f fr)
    apply (F.iso hrotx.hom).inv.app (repO x).ia ≫ _ ≫ (F.iso hroty.hom).hom.app (repO y).ia

    let t := IsFiltered.max tx.a ty.a
    have jx : tx.a ⟶ t := IsFiltered.leftToMax tx.a ty.a
    have jy : ty.a ⟶ t := IsFiltered.rightToMax tx.a ty.a

    apply (F.iso jx).inv.app _ ≫ _ ≫ (F.iso jy).hom.app _

    simp
    apply (F.i t).map


    sorry

def truc : IsColimitF i _ iaSubC where
  desc := by
    intro B
    sorry
  fac := by

    sorry
  uniq := sorry



end

noncomputable section -- pour avoir au moins une situation ou ce qui précède s'applique

variable {X : Type u1} [TopologicalSpace X] [T2Space X] (K : Compacts X)
variable {D : Type u2} [Category.{u2, u2} D] (F : (Opens X)ᵒᵖ ⥤ D)

@[simps]
def iEx : (supSupK_cat K)ᵒᵖ  ⥤ Cat where
  obj L := Cat.of (KsubU_cat L.unop.obj trueCond)ᵒᵖ
  map f := Functor.op (K1subK2subU _ ((ObjectProperty.ι _ ).map f.unop))

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

def FcupIaEx  : (KsubU_cat K trueCond)ᵒᵖ ⥤ D := (ObjectProperty.ι _ ).op ⋙ F

#check CoconeFWhisker _ (iaSubCEx K) (FcupIaEx K F)

variable [HasColimitsOfSize.{u1, u1, u2, u2} D]

#check colimFia (iaSubCEx K) (FcupIaEx K F)

variable [LocallyCompactSpace X]

variable (repCompat : (x : C) → (r1 r2 : repObj iaSubC x) → ∃ g : r1.a ⟶ r2.a, (i.map g).obj r1.ia = r2.ia ∨ ∃ g : r2.a ⟶ r1.a, (i.map g).obj r2.ia = r1.ia )


@[simps]
def repOEx (U : (KsubU_cat K trueCond)ᵒᵖ) : (repObj (iaSubCEx K) U ) where
  a := by
    let ⟨L,hL⟩ := Classical.choice (existsIntermed X K U.unop.obj U.unop.property.1)
    apply op
    use ⟨L, hL.1⟩
    use ⟨interior L, isOpen_interior⟩
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

omit [LocallyCompactSpace X] [T2Space X] in
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
    apply ObjectProperty.FullSubcategory.ext
    simp_all only [iaSubCEx, iaSubCExi, iaExEqU K r, iaExEqU K s, le_refl, inf_of_le_left]

@[simps]
def liftingToSupLeft {U : (KsubU_cat K trueCond)ᵒᵖ}  (r s : repObj (iaSubCEx K) U) : lifting (iaSubCEx K) r (resupEx K r s) where
  hom := op <| InfInLeftSSK K (unop r.a) (unop s.a)
  liftIso := by
    apply eqToIso
    simp [K1subK2subU]
    apply ObjectProperty.FullSubcategory.ext
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
    apply ObjectProperty.FullSubcategory.ext
    simp [iaExEqU K r, iaExEqU K s]
  compat := by
    simp only [iaSubCEx, iaSubCExi]
    rfl

def repLiftingEx {U : (KsubU_cat K trueCond)ᵒᵖ}  (r s : repObj (iaSubCEx K) U) : (t : repObj (iaSubCEx K) U) × (lifting (iaSubCEx K) r t) × (lifting (iaSubCEx K) s t) := by
  use resupEx K r s
  constructor
  · apply liftingToSupLeft
  · apply liftingToSupRight


#check colimColimIsColim (iaSubCEx K) (FcupIaEx K F) (repOEx K) (repHEx K) (repLiftingEx K)

--#lint
