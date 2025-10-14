--import Mathlib
import M2.KsubU
import M2.RCalpha
import M2.forceColimW

open CategoryTheory Limits TopologicalSpace Compacts Opposite Functor

universe u1 u2 u3 u4 v1 v2 v3 v4

section
variable {A : Type u1} [Category.{v1, u1} A] {B : Type u3} [Category.{v3, u3} B]
variable (F : A ⥤ Cat.{v2, u2})

/-- The isomorphism one imagine (induced by equality) between (F.map (𝟙 _) ⋙ (G a) and  (G a)-/
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

/-- The isomorphism one imagine (induced by the equality F.map (f ≫ g) = F.map f ≫ F.map g ) between F.map (f ≫ g) ⋙ G c and G a-/
@[simps!]
def FmapCompGIso (F : A ⥤ Cat.{v2, u2}) (G : (a : A) → (F.obj a) ⥤ B) (iso : { a b : A} → (f : a ⟶ b) → (F.map f) ⋙ G b ≅ G a) {a b c : A } (f : a ⟶ b) (g :b ⟶ c) : F.map (f ≫ g) ⋙ G c ≅ G a := isoWhiskerRight (eqToIso (F.map_comp _ _)) (G c) ≪≫ associator (F.map f) (F.map g) (G c) ≪≫ isoWhiskerLeft (F.map f) (iso g) ≪≫ iso f

variable (B : Type u3) [Category.{v3, u3} B]
/-- The data of a Cocone for F, but with isomorphism instead of equality and the lemmas that allow computation

B is not part of the structure to avoid issue in inferance later-/
structure CoconeFunctor (F : A ⥤ Cat.{v2, u2}) where
  /-- the canonial morphisms of the cocone-/
  i : (x : A) → (F.obj x) ⥤ B
  /-- The w condition of the cocone as an isomorphism-/
  iso : { x y : A} → (f : x ⟶ y) → (F.map f) ⋙ i y ≅ i x
  /-- The compatibility condition over iso 𝟙 _-/
  isoId : (x  : A) → (iso (𝟙 x)) = GIdIso F i x
  /-- The compatibility condition over iso(f ≫ g)-/
  isoComp : {x y z: A } → (f : x ⟶ y) → (g : y ⟶ z) → (iso (f ≫ g) = FmapCompGIso F i iso f g)

/-structure IsColimitF (t : CoconeFunctor B F) where
  desc : {C : Cat.{v4, u4}} → (s : CoconeFunctor C F) → B ⥤ C
  fac : {C : Cat.{v4, u4}} → (s : CoconeFunctor C F) → (a : A) → (t.i a) ⋙ desc s = (s.i a)--probablement à transformer en iso plus tard
  uniq : {C : Cat.{v4, u4}} → (s : CoconeFunctor C F) → (m : B ⥤ C) → (∀ (a : A), (t.i a) ⋙ m = (s.i a)) → m = desc s-/

variable {B : Type u3} [Category.{v3, u3} B] {C : Type u4} [Category.{v4, u4} C]

/-- Build a new CoconeFunctor by whiskering the data to the right-/
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

/-- The cocone induced by applying FcupIa to the diagram i. It's not a @[simp] so that simp try to find solution without unfolding it (for exemple in the def colimFia)-/
def F : CoconeFunctor D i := CoconeFWhisker i iaSubC FcupIa

--variable (h : IsColimitF i C iaSubC)

/-lemma bidule : FcupIa = @h.desc _ _ (Cat.of D) (F iaSubC FcupIa)  := by
  apply @h.uniq  _ _ (Cat.of D) (F iaSubC FcupIa)
  intro a
  simp [F]-/

variable (a : A)

--variable [(a : A) → HasLimitsOfSize.{v3, u3} (i.obj a)]

noncomputable section

variable [HasColimitsOfSize.{v4, u4} D]

/-- The diagram a ↦ colim_(i.obj a) Fia-/
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

/-- Data that allow to represent x : C as an element (a, ia) -/
structure repObj (x : C) where
  /-- The index in which the representant leaves-/
  a : A
  /-- The representant of x-/
  ia : i.obj a
  /-- The isomorphism that shows that ia represent x-/
  rep : (iaSubC.i a).obj ia ≅ x

/-- Data that allow to represent f : x ⟶ y as an element (a, ia1) ⟶ (a,ia2) -/
structure repHom {x y : C} (f : x ⟶ y) where
  /-- The index in which the representant leaves-/
  a : A
  /-- The representant of x-/
  iaDom : i.obj a
  /-- The representant of y-/
  iaCoDom : i.obj a
  /-- The isomorphism that shows that iaDom represent x-/
  repDom : (iaSubC.i a).obj iaDom ≅ x
  /-- The isomorphism that shows that iaCodom represent y-/
  repCoDom : (iaSubC.i a).obj iaCoDom ≅ y
  /-- Th representant of f-/
  hom : iaDom ⟶ iaCoDom
  /-- The isomorphism that shows that hom represent f-/
  rep : repDom.inv ≫(iaSubC.i a).map hom ≫ repCoDom.hom = f

/-- Data that express the compatibility between two reprsentation of x : C-/
structure lifting {x : C} (r s : repObj iaSubC x) where
  /-- The lifting between indexes-/
  hom : r.a ⟶ s.a
  /-- the isomorphism that shows that hom is a lifting-/
  liftIso : (i.map hom).obj r.ia ≅ s.ia
  /-- The compatilty condition between the liftings and the representing morphisms of r and s-/
  compat : r.rep.hom ≫ s.rep.inv = ((iaSubC.iso hom).inv).app r.ia ≫ (iaSubC.i s.a).map liftIso.hom

variable (repO : (x : C) → repObj iaSubC x)
variable (repH : {x y : C} → ( f: x ⟶ y) → repHom iaSubC f)

/-- The representation of the domain induced by a representation of a morphism-/
@[simps]
def repHtoD {x y : C} (f : x ⟶ y) (r : repHom iaSubC f) : (repObj iaSubC x) := ⟨r.a,r.iaDom,r.repDom⟩

/-- The representation of the codomain induced by a representation of a morphism-/
@[simps]
def repHtoCd {x y : C} (f : x ⟶ y) (r : repHom iaSubC f) : (repObj iaSubC y) := ⟨r.a,r.iaCoDom,r.repCoDom⟩

/-- The tautologic representation of an element (a, ia)-/
@[simps]
def repCanO (a : A) (x : i.obj a) : repObj iaSubC ((iaSubC.i a).obj x) where
  a := a
  ia := x
  rep := eqToIso rfl

/-- if r anq s are two compatible then the morphism FcupIa.obj x → colimit induced by the two representation are compatible with the structure of diagram of colimFia-/
@[simp]
lemma FcupColimIndepOfLift {x : C}  (r s : repObj iaSubC x) (l : lifting iaSubC r s) : (FcupIa.map r.rep.inv ≫ colimit.ι ((F iaSubC FcupIa).i r.a) r.ia) ≫ (colimFia iaSubC FcupIa).map l.hom = FcupIa.map s.rep.inv ≫ colimit.ι ((F iaSubC FcupIa).i s.a) s.ia := by
  have : s.rep.inv = r.rep.inv ≫ ((iaSubC.iso l.hom).inv).app r.ia ≫ (iaSubC.i s.a).map l.liftIso.hom := by
    rw [ ← l.compat]
    simp

  rw [this, FcupIa.map_comp]
  repeat rw [ Category.assoc]
  apply whisker_eq

  suffices FcupIa.map ((iaSubC.iso l.hom).inv.app r.ia) ≫ colimit.ι (iaSubC.i s.a ⋙ FcupIa) ((i.map l.hom).obj r.ia) = FcupIa.map ((iaSubC.iso l.hom).inv.app r.ia) ≫
    FcupIa.map ((iaSubC.i s.a).map l.liftIso.hom) ≫ colimit.ι (iaSubC.i s.a ⋙ FcupIa) s.ia by simp [F]; assumption

  apply whisker_eq
  --here rw [← colimit.w ]; rfl works but we have the tactic...
  forceColimW

/-If the representation r is a lifting of the representation q then the morphism _ ≫ colimit.ι _ ≫ colimit.ι _ is the same for r and q.
The lemma is valid for any cocone not just the colimit-/
@[simp]
lemma colimColimIndepOfLift (x : C) (s : Cocone (colimFia iaSubC FcupIa) ) (r q : repObj iaSubC x) (l : lifting iaSubC r q) : FcupIa.map r.rep.inv ≫ colimit.ι (iaSubC.i r.a ⋙ FcupIa) r.ia ≫ s.ι.app r.a = FcupIa.map q.rep.inv ≫ colimit.ι (iaSubC.i q.a ⋙ FcupIa) q.ia ≫ s.ι.app q.a := by
  have : (colimFia iaSubC FcupIa).map l.hom ≫ s.ι.app q.a = s.ι.app r.a := by
      rw [s.ι.naturality]
      simp
  rw [← this]
  repeat rw [← Category.assoc]
  apply eq_whisker
  apply FcupColimIndepOfLift

variable (repLifting : {x : C} → (r s : repObj iaSubC x) → (t : repObj iaSubC x) × (lifting iaSubC r t) × (lifting iaSubC s t))

/- Same statement as colimColimIndepOfLift with no hypothesis on r and q bu assuming there is a general construction that give a common lifting -/
include repLifting in
theorem colimColimIndep {x : C} (s : Cocone (colimFia iaSubC FcupIa) ) (r q : repObj iaSubC x) : FcupIa.map r.rep.inv ≫ colimit.ι (iaSubC.i r.a ⋙ FcupIa) r.ia ≫ s.ι.app r.a = FcupIa.map q.rep.inv ≫ colimit.ι (iaSubC.i q.a ⋙ FcupIa) q.ia ≫ s.ι.app q.a := by
  let ⟨t, lrt, lqt⟩ := repLifting r q
  rw [colimColimIndepOfLift _ _ _ _ _ t lrt]
  rw [colimColimIndepOfLift _ _ _ _ _ t lqt]

/-- the natural transformation involved in colimColimFiaCoconeFcupIa-/
@[simps]
def colimColimFiaCoconeFcupIaι (s : Cocone (colimFia iaSubC FcupIa) ) : FcupIa ⟶ (const C).obj s.pt where
  app x := let xr := repO x;
      (FcupIa.map xr.rep.inv ≫ colimit.ι (iaSubC.i xr.a ⋙ FcupIa) xr.ia) ≫ s.ι.app xr.a
  naturality x y f:= by
    let fr := repH f
    suffices FcupIa.map f ≫ _ = _ by simpa

    rw [colimColimIndep iaSubC FcupIa repLifting s (repO y) (repHtoCd iaSubC f fr)]
    rw [colimColimIndep iaSubC FcupIa repLifting s (repO x) (repHtoD iaSubC f fr)]

    suffices FcupIa.map f ≫ FcupIa.map fr.repCoDom.inv ≫ colimit.ι (iaSubC.i fr.a ⋙ FcupIa) fr.iaCoDom ≫ s.ι.app fr.a = FcupIa.map fr.repDom.inv ≫ colimit.ι (iaSubC.i fr.a ⋙ FcupIa) fr.iaDom ≫ s.ι.app fr.a by simpa

    -- ce serait cool d'avoir forceColimW qui s'occupe de ça mais on verra plus tard

    rw [← colimit.w ((iaSubC.i fr.a ⋙ FcupIa)) fr.hom]
    rw [← Category.assoc]

    slice_lhs 1 1 => rw [← fr.rep]
    simp

/-- If s is a cocone for colimFia then it induces a cocone over FcupIa with the same point-/
@[simps]
def colimColimFiaCoconeFcupIa (s : Cocone (colimFia iaSubC FcupIa) ) : Cocone FcupIa where
  pt := s.pt
  ι := colimColimFiaCoconeFcupIaι _ _ repO repH repLifting s

/-
include repLifting
@[simp]
theorem colimColimIndep {x : C}  (r s : repObj iaSubC x) : FcupIa.map r.rep.inv ≫ colimit.ι ((F iaSubC FcupIa).i r.a) r.ia ≫ colimit.ι (colimFia iaSubC FcupIa ) r.a = FcupIa.map s.rep.inv ≫ colimit.ι ((F iaSubC FcupIa).i s.a) s.ia ≫ colimit.ι (colimFia iaSubC FcupIa ) s.a := by
  exact machin6 iaSubC FcupIa repLifting (colimit.cocone (colimFia iaSubC FcupIa)) r s
-/


/--The natural transformation involved in fCupIaConeToFiaCone-/
@[simps]
def fCupIaCoconeToFiaCoconeι (s : Cocone FcupIa) : (F iaSubC FcupIa).i a ⟶ (const (i.obj a)).obj s.pt where
  app x := s.ι.app ((iaSubC.i a).obj x)
  naturality _ _ _ := by
    simp [F]

/-- For any a the cocone structure over Fia of a cocone over FcupIa-/
@[simps]
def fCupIaCoconeToFiaCocone (s : Cocone FcupIa) : Cocone ((F iaSubC FcupIa).i a) where
  pt := s.pt
  ι := fCupIaCoconeToFiaCoconeι iaSubC FcupIa a s

/--The natural transformation involved in fCupIaConeToLimFiaCone-/
@[simps]
def fCupIaCoconeToColimFiaCoconeι (s : Cocone FcupIa) : colimFia iaSubC FcupIa ⟶ (const A).obj s.pt where
  app a := colimit.desc _ (fCupIaCoconeToFiaCocone iaSubC FcupIa a s)
  naturality _ _ _:= by
    apply colimit.hom_ext
    intro
    simp [F]

/-- The cocone structure  over lim FIa of a cocone over FcupIa with the same point-/
@[simps]
def fCupIaCoconeToColimFiaCocone (s : Cocone FcupIa ) : Cocone (colimFia iaSubC FcupIa) where
  pt := s.pt
  ι := fCupIaCoconeToColimFiaCoconeι iaSubC FcupIa s


variable [HasColimitsOfSize.{v1, u1} D]

/-- The evidence that the colimit of colimit is a colimit over the "union of indexes"-/
@[simps]
def colimColimIsColim (s : Cocone (colimFia iaSubC FcupIa)) (hs : IsColimit s) : IsColimit (colimColimFiaCoconeFcupIa iaSubC FcupIa repO repH repLifting s) where
  desc t :=hs.desc (fCupIaCoconeToColimFiaCocone iaSubC FcupIa t)
  fac s x := by
    simp [F]
  uniq t (m : s.pt ⟶ t.pt) hm := by
    apply hs.uniq (fCupIaCoconeToColimFiaCocone iaSubC FcupIa t)
    intro a

    apply colimit.hom_ext
    intro x

    suffices colimit.ι ((F iaSubC FcupIa).i a) x ≫ s.ι.app a ≫ m = t.ι.app ((iaSubC.i a).obj x) by simpa

    rw [← hm _]

    repeat rw [← Category.assoc]
    apply eq_whisker

    suffices colimit.ι (iaSubC.i a ⋙ FcupIa) x ≫ s.ι.app a = FcupIa.map (repO ((iaSubC.i a).obj x)).rep.inv ≫ colimit.ι (iaSubC.i (repO ((iaSubC.i a).obj x)).a ⋙ FcupIa) (repO ((iaSubC.i a).obj x)).ia ≫ s.ι.app (repO ((iaSubC.i a).obj x)).a by simpa [F]

    rw [← colimColimIndep iaSubC FcupIa repLifting s (repCanO iaSubC a x) (repO ((iaSubC.i a).obj x))]
    simp


variable [HasColimitsOfSize.{v2, u2} D]

/-- The evidence that the colimit over the "union of indexes" is the colimit of the colimit-/
@[simps]
def colimIsColimColim ( s : Cocone FcupIa) (hs : IsColimit s): IsColimit (fCupIaCoconeToColimFiaCocone iaSubC FcupIa s) where
  desc t := hs.desc (colimColimFiaCoconeFcupIa iaSubC FcupIa repO repH repLifting t)
  fac t a := by
    apply colimit.hom_ext
    intro x
    suffices FcupIa.map (repO ((iaSubC.i a).obj x)).rep.inv ≫
    colimit.ι (iaSubC.i (repO ((iaSubC.i a).obj x)).a ⋙ FcupIa) (repO ((iaSubC.i a).obj x)).ia ≫
      t.ι.app (repO ((iaSubC.i a).obj x)).a =
  colimit.ι ((F iaSubC FcupIa).i a) x ≫ t.ι.app a by simpa

    rw [ ← colimColimIndep iaSubC FcupIa repLifting t (repCanO iaSubC a _) (repO ((iaSubC.i a).obj _))]
    simp [F]
  uniq t (m : s.pt ⟶ t.pt) hm := by
    apply hs.uniq (colimColimFiaCoconeFcupIa iaSubC FcupIa repO repH repLifting  t)
    intro
    simp [ ← hm _, F]

/-variable (G: A ⥤ D) (Giso : G ≅ colimFia iaSubC FcupIa) (s : Cocone G) (t : Cocone (colimFia iaSubC FcupIa)) ( ht : IsColimit t)

def truc (h : s ≅ (Cocones.precomposeEquivalence Giso ).functor.obj t) : IsColimit s := by

  apply Limits.IsColimit.ofIsoColimit _ h.symm
  apply IsColimit.ofPreservesCoconeInitial




  sorry
  --apply colimIsColimColim _ _ (repOEx K) (repHEx K) (repLiftingEx K) _-/








/-test pour voir si C peut être une colimite

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
  uniq := sorry-/



end

noncomputable section -- the exemple that will be applyed in the fille alpha_K_sheaf.lean

variable {X : Type u1} [TopologicalSpace X] [T2Space X] (K : Compacts X)
variable {D : Type u2} [Category.{v2, u2} D] (F : (Opens X)ᵒᵖ ⥤ D)

/-- The diagram of diagram ( L ⊆ U) indexed by L compacts neighbourhoods of K-/
@[simps]
def iEx : (supSupK_cat K)ᵒᵖ  ⥤ Cat where
  obj L := Cat.of (KsubU_cat L.unop.obj trueCond)ᵒᵖ
  map f := Functor.op (K1subK2subU _ ((ObjectProperty.ι _ ).map f.unop))

/-- The functor to the "union category of indexes" that just forget the L in (K ⊆ L ⊆ U)-/
@[simps]
def iaSubCExi (L : (supSupK_cat K)ᵒᵖ ) : ((iEx K ).obj L) ⥤ (KsubU_cat K trueCond)ᵒᵖ  where
  obj U := ⟨U.unop.obj,⟨Set.Subset.trans (supSupKtoSupK K (unop L)) (unop U).property.left, of_eq_true (eq_self true)⟩⟩
  map f := op <| homOfLE <| leOfHom f.unop

/-- The coconeFunctor structure over iaSubCExi (which are comming from equality)-/
@[simps]
def iaSubCEx : CoconeFunctor (KsubU_cat K trueCond)ᵒᵖ (iEx K) where
  i := iaSubCExi K
  iso _ := eqToIso rfl
  isoId _ := rfl
  isoComp _ _ := rfl

/-- The version of F with domain the "union category"-/
def FcupIaEx  : (KsubU_cat K trueCond)ᵒᵖ ⥤ D := (ObjectProperty.ι _ ).op ⋙ F

#check CoconeFWhisker _ (iaSubCEx K) (FcupIaEx K F)

variable [HasColimitsOfSize.{u1, u1, v2, u2} D]

#check colimFia (iaSubCEx K) (FcupIaEx K F)

variable [LocallyCompactSpace X]

variable (repCompat : (x : C) → (r1 r2 : repObj iaSubC x) → ∃ g : r1.a ⟶ r2.a, (i.map g).obj r1.ia = r2.ia ∨ ∃ g : r2.a ⟶ r1.a, (i.map g).obj r2.ia = r1.ia )

/-- a representation of (K ⊆ U) as (K ⊆ L ⊆ U) with L that exists because of the space being locally compact-/
@[simps]
def repOEx (U : (KsubU_cat K trueCond)ᵒᵖ) : (repObj (iaSubCEx K) U ) where
  a := by
    let ⟨L,hL⟩ := Classical.choice (existsIntermedKAndU X K U.unop.obj U.unop.property.1)
    apply op
    use ⟨L, hL.1⟩
    use ⟨interior L, isOpen_interior⟩
    constructor
    exact hL.2.1
    exact interior_subset
  ia := op ⟨U.unop.obj, by
      constructor
      exact (Classical.choice (existsIntermedKAndU X K U.unop.obj U.unop.property.1)).2.2.2
      rfl⟩
  rep := eqToIso rfl

/-- a representation of a morphism (there is no choice because of the unique morphism in ordered set) -/
@[simps]
def repHEx {U V : (KsubU_cat K trueCond)ᵒᵖ} (f : U ⟶ V) : repHom (iaSubCEx K) f where
  a := (repOEx K V).a
  iaDom := ⟨U.unop.obj, by
    constructor
    apply Set.Subset.trans _ (leOfHom f.unop)
    exact (Classical.choice (existsIntermedKAndU X K V.unop.obj V.unop.property.1)).2.2.2
    simp⟩
  iaCoDom := (repOEx K V).ia
  repDom := Iso.refl _
  repCoDom := (repOEx K V).rep
  hom := op <| homOfLE ( leOfHom f.unop)
  rep := rfl

omit [LocallyCompactSpace X] [T2Space X] in
lemma iaExEqU {U : (KsubU_cat K trueCond)ᵒᵖ} (r : repObj (iaSubCEx K) U) : (unop r.ia).obj = (unop U).obj := antisymm (leOfHom (r.rep.inv.unop)) (leOfHom (r.rep.hom.unop))

/-- a representant lifting two reprentant : send (K ⊆ Li ⊆ U)_i to (K ⊆ L1 ∩ L2 ⊆ U)-/
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

/-- The morphism commint with resupEx to the left , again no choice for the morphisms-/
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

/-- The morphism commint with resupEx to the right , again no choice for the morphisms-/
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

/-- Combining the three previous definition into a replifting data-/
def repLiftingEx {U : (KsubU_cat K trueCond)ᵒᵖ}  (r s : repObj (iaSubCEx K) U) : (t : repObj (iaSubCEx K) U) × (lifting (iaSubCEx K) r t) × (lifting (iaSubCEx K) s t) := by
  use resupEx K r s
  constructor
  · apply liftingToSupLeft
  · apply liftingToSupRight


#check colimColimIsColim (iaSubCEx K) (FcupIaEx K F) (repOEx K) (repHEx K) (repLiftingEx K)

--#lint
