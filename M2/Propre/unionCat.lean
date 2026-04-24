import M2.Propre.Topology
import M2.forceColimW

open CategoryTheory Limits TopologicalSpace Compacts Opposite Functor

universe u1 u2 u3 u4 v1 v2 v3 v4

namespace CategoryTheory.Limits.UnionCat
variable {A : Type u1} [Category.{v1, u1} A] {I : A ⥤ Cat.{v2, u2}} {D : Type u3} [Category.{v3, u3} D]

variable (D) in
/-- The data of a Cocone for F, but with isomorphism instead of equality and the lemmas that allow computation

D is not part of the structure to avoid issue in inferance later-/
structure CoconeFunctor (I : A ⥤ Cat.{v2, u2}) where
  /-- the canonial morphisms of the cocone-/
  i : (x : A) → (I.obj x) ⥤ D
  /-- The w condition of the cocone as an isomorphism-/
  iso : { x y : A} → (f : x ⟶ y) → (I.map f).toFunctor ⋙ i y ≅ i x
  /-- The compatibility condition over iso 𝟙 _ : it equals the isomorphism induced by equality between (I.map (𝟙 _) ⋙ (G a) and  (G a)-/
  isoId : (x  : A) → (iso (𝟙 x)) = eqToIso (by simp [Functor.id_comp])
  /-- The compatibility condition over iso(f ≫ g): it equals the isomorphism induced by equality F.map (f ≫ g) = F.map f ≫ F.map g )-/
  isoComp : {x y z: A } → (f : x ⟶ y) → (g : y ⟶ z) → iso (f ≫ g) = isoWhiskerRight (eqToIso ((Cat.ext_iff.mp (I.map_comp _ _)).trans (Cat.Hom.comp_toFunctor _ _))) (i z) ≪≫ associator (I.map f).toFunctor (I.map g).toFunctor (i z) ≪≫ isoWhiskerLeft (I.map f).toFunctor (iso g) ≪≫ iso f

variable {C : Type u4} [Category.{v4, u4} C] (sD : CoconeFunctor D I)


attribute [local simp] UnionCat.CoconeFunctor.isoId eqToHom_map UnionCat.CoconeFunctor.isoComp
/-- Build a new CoconeFunctor by whiskering the data to the right-/
@[simps]
def  CoconeFunctor.extend (H : D ⥤ C) : CoconeFunctor C I where
i x := sD.i x ⋙ H
iso f := (I.map f).toFunctor.associator  (sD.i _) H ≪≫ (isoWhiskerRight (sD.iso f) H)
isoId := by aesop_cat
isoComp := by aesop_cat

--variable {I} in
/- The cocone induced by applying FcupIa to the diagram i. It's not a @[simp] so that simp try to find solution without unfolding it (for exemple in the def colimFia)-/
--def F : CoconeFunctor C I := s.extend FcupIa

attribute [local simp] colimit.eqToHom_comp_ι
set_option backward.isDefEq.respectTransparency false in
/-- The diagram a ↦ colim_(I.obj a) I.i a-/
@[simps]
noncomputable def CoconeFunctor.colim [HasColimitsOfSize.{v2, u2} D]: A ⥤ D where
  obj a := colimit (sD.i a)
  map f := (HasColimit.isoOfNatIso (sD.iso f).symm).hom ≫ colimit.pre (sD.i _) (I.map f).toFunctor

/-- Data that allow to represent x : D as an element (a, ia) -/
structure repObj (x : D) where
  /-- The index in which the representant leaves-/
  a : A
  /-- The representant of x-/
  ia : I.obj a
  /-- The isomorphism that shows that ia represent x-/
  rep : (sD.i a).obj ia ≅ x

/-- Data that allow to represent f : x ⟶ y as an element (a, ia1) ⟶ (a,ia2) -/
structure repHom {x y : D} (f : x ⟶ y) where
  /-- The index in which the representant leaves-/
  a : A
  /-- The representant of x-/
  iaDom : I.obj a
  /-- The representant of y-/
  iaCoDom : I.obj a
  /-- The isomorphism that shows that iaDom represent x-/
  repDom : (sD.i a).obj iaDom ≅ x
  /-- The isomorphism that shows that iaCodom represent y-/
  repCoDom : (sD.i a).obj iaCoDom ≅ y
  /-- Th representant of f-/
  hom : iaDom ⟶ iaCoDom
  /-- The isomorphism that shows that hom represent f-/
  rep : repDom.inv ≫(sD.i a).map hom ≫ repCoDom.hom = f

variable {sD} in
/-- Data that express the compatibility between two reprsentation of x : C-/
structure lifting {x : D} (r s : repObj sD x) where
  /-- The lifting between indexes-/
  hom : r.a ⟶ s.a
  /-- the isomorphism that shows that hom is a lifting-/
  liftIso : (I.map hom).toFunctor.obj r.ia ≅ s.ia
  /-- The compatilty condition between the liftings and the representing morphisms of r and s-/
  compat : r.rep.hom ≫ s.rep.inv = ((sD.iso hom).inv).app r.ia ≫ (sD.i s.a).map liftIso.hom

/-- The representation of the domain induced by a representation of a morphism-/
@[simps]
def repHtoD {x y : D} (f : x ⟶ y) (r : repHom sD f) : (repObj sD x) := ⟨r.a,r.iaDom,r.repDom⟩

/-- The representation of the codomain induced by a representation of a morphism-/
@[simps]
def repHtoCd {x y : D} (f : x ⟶ y) (r : repHom sD f) : (repObj sD y) := ⟨r.a,r.iaCoDom,r.repCoDom⟩

/-- The tautologic representation of an element (a, ia)-/
@[simps]
def repCanO (a : A) (x : I.obj a) : repObj sD ((sD.i a).obj x) where
  a := a
  ia := x
  rep := eqToIso rfl

structure unionCat where
  sD : CoconeFunctor D I
  repO : (x : D) → repObj sD x
  repH : {x y : D} → ( f: x ⟶ y) → repHom sD f
  repLifting : {x : D} → (r s : repObj sD x) → (t : repObj sD x) × (lifting r t) × (lifting s t)
