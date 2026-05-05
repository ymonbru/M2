import M2.Propre.Topology
import M2.forceColimW
import Mathlib

open CategoryTheory Limits TopologicalSpace Compacts Opposite Functor Pseudofunctor.StrongTrans

universe u1 u2 u3 u4 v1 v2 v3 v4
namespace CategoryTheory.Bicategory
variable {B C : Type*} [Bicategory B] [Bicategory C]
variable {F : B ⥤ᵖ C}

@[simps]
def Pseudofunctor.constObj {J C : Type*} [Bicategory J] [Bicategory C] (x : C) : J ⥤ᵖ C where
  obj _ := x
  map _ := 𝟙 _
  map₂ _ := 𝟙 _
  mapId _ := eqToIso rfl
  mapComp _ _ := (λ_ (𝟙 x)).symm


set_option backward.isDefEq.respectTransparency false in
@[simps]
def Pseudofunctor.constMap {J C : Type*} [Bicategory J] [Bicategory C] {x y : C } (f : x ⟶ y) : Pseudofunctor.constObj (J := J) x ⟶ Pseudofunctor.constObj y  where
app _ := f
naturality j := bicategoricalIso (𝟙 x ≫ f) (f ≫ 𝟙 y)

set_option backward.isDefEq.respectTransparency false in
@[simps]
def PseudoFunctor.constMap₂ {J C : Type*} [Bicategory J] [Bicategory C] {x y : C } {f g: x ⟶ y} (τ : f ⟶ g) : Pseudofunctor.constMap (J := J) f ⟶ Pseudofunctor.constMap g  where
  as := ⟨ fun _ => τ, fun _ => by simp [Pseudofunctor.constMap]⟩

set_option backward.isDefEq.respectTransparency false in
@[simps]
def Pseudofunctor.const {C : Type*} (J : Type*) [Bicategory J] [Bicategory C] : C ⥤ᵖ J ⥤ᵖ C where
  obj := Pseudofunctor.constObj
  map := Pseudofunctor.constMap
  map₂ := PseudoFunctor.constMap₂
  mapId _ := by
    refine Pseudofunctor.StrongTrans.isoMk ?_ ?_
    · intro _
      rfl
    · intro _ _ _
      simp
  mapComp _ _ := by
    refine Pseudofunctor.StrongTrans.isoMk ?_ ?_
    · intro _
      rfl
    · intro _ _ _
      simp

#check Pseudofunctor.const

variable (F) in
structure Cocone where
  pt : C
  ι : Pseudofunctor.StrongTrans F ((Pseudofunctor.const B).obj pt)

--def Cocone.w (s : Cocone F) {x y : B} (f : x ⟶ y) : F.map f ≫ s.ι.app x ≅ s.ι.app y := by sorry
@[simps]
def Cocone.extend (c : Cocone F) {x : C} (f : c.pt ⟶ x ) : Cocone F where
  pt := x
  ι := c.ι ≫ (Pseudofunctor.const B).map f

def Cocone.whisker {D : Type*} [Bicategory D] (E : D ⥤ᵖ B) (c : Cocone F) : Cocone (E.comp F) where
  pt := c.pt
  ι := by

    --est-ce que j'ai vraiment besoin de ça?
    sorry



variable {B : Type u1 } [Category.{v1, u1} B]
variable {I : LocallyDiscrete B ⥤ᵖ Cat.{v2, u2}} (c : Cocone I)

set_option backward.isDefEq.respectTransparency false in
@[simps]
def truc : I.Grothendieck ⥤ c.pt where
  obj g := (c.ι.app ⟨g.1⟩).toFunctor.obj g.2
  map {g h} f := (c.ι.naturality f.1.toLoc).inv.toNatTrans.app g.2 ≫ (c.ι.app ⟨h.1⟩).toFunctor.map f.2
  map_id x := by
    suffices (c.ι.app ⟨x.base⟩).toFunctor.map _ = (c.ι.naturality _ ).hom.toNatTrans.app x.fiber  by
      rw [this]
      simp
    have : (c.ι.naturality (𝟙 x : x ⟶ x).base.toLoc ).hom = ?_ := by simpa using c.ι.naturality_id ⟨x.1⟩

    rw [this]
    simp
  map_comp {x y z } f g:= by

    suffices (c.ι.app { as := z.base }).toFunctor.map (f ≫ g).fiber = (c.ι.naturality (f ≫ g).base.toLoc).hom.toNatTrans.app x.fiber ≫ ?_ by
      rw [this, ← Category.assoc]
      simp
      rfl

    let h := c.ι.naturality_comp f.1.toLoc g.1.toLoc
    --let h := NatTrans.ext_iff.1 (Cat.Hom₂.ext_iff.1 (c.ι.naturality_comp f.1.toLoc g.1.toLoc))

    simp at h

    have : (c.ι.naturality (f.base.toLoc ≫ g.base.toLoc)).hom = ?_ ≫ (α_ (c.ι.app { as := x.base }) (𝟙 c.pt) (𝟙 c.pt)).inv≫ (ρ_ (c.ι.app { as := x.base } ≫ 𝟙 c.pt)).hom := by
      --simpa using h
      sorry

    --rw [← h]
    sorry
    sorry

instance : IsCofilteredOrEmpty I.Grothendieck where
  cone_objs d1 d2 := by




    sorry
  cone_maps d1 d2 f1 f2 := by


    sorry

instance : (truc c).Initial := by
  rw [Functor.initial_iff_of_isCofiltered]
  constructor
  · intro d
    simp
    sorry
  · intro d ⟨a,x⟩ f1 f2
    simp at f1
    simp at f2
    simp

    sorry

variable {D : Cat}
variable (F : c.pt ⟶ D)

#check Bicategory.Cocone.extend c

set_option backward.isDefEq.respectTransparency false in
lemma hey : truc (c.extend F) = truc c ⋙ F.toFunctor := Functor.ext (by simp) (by simp)

set_option backward.isDefEq.respectTransparency false in
@[simps]
noncomputable def CoconeFunctor.colim [HasColimitsOfSize.{v2, u2} c.pt] : B ⥤ c.pt where
  obj a := colimit (c.ι.app ⟨a⟩).toFunctor
  map {a b} f := by
    have : HasColimit.{v2, u2} (c.ι.app { as := b }).toFunctor := by
      sorry
    have : HasColimit ((I.map { as := f }).toFunctor ⋙ (c.ι.app { as := b }).toFunctor) := by sorry

    #check I.map

    refine ?_ ≫ colimit.pre (c.ι.app ⟨b⟩).toFunctor (I.map ⟨f⟩).toFunctor



    apply (HasColimit.isoOfNatIso _ ).hom


    --#check (c.ι.naturality ⟨f⟩).symm
    simp at iso
    #check Functor.mapIso Cat.Hom.toFunctor

    #check HasColimit.isoOfNatIso iso
    sorry--(HasColimit.isoOfNatIso (s.iso f).symm).hom ≫ colimit.pre (sD.i _) (I.map f).toFunctor
  map_id := sorry
  map_comp := sorry




end CategoryTheory.Bicategory

namespace CategoryTheory.Limits.UnionCat
variable {A : Type u1} [Category.{v1, u1} A] {D : Type u3} [Category.{v3, u3} D]
variable {I : A ⥤ Cat.{v2, u2}}

#check I.toPseudofunctor'

#check Pseudofunctor.Grothendieck.forget

--#check Pseudofunctor.StrongTrans I.toPseudofunctor' ((Functor.const A).obj self.pt).toPseudofunctor'

variable (I) in
structure test  where
  pt : Cat
  ι : Pseudofunctor.StrongTrans I.toPseudofunctor' ((Functor.const A ).obj pt).toPseudofunctor'

variable (D I) in
/-- The data of a Cocone for F, but with isomorphism instead of equality and the lemmas that allow computation

D is not part of the structure to avoid issue in inferance later-/
structure CoconeFunctor where
  /-- the canonial morphisms of the cocone-/
  i : (x : A) → (I.obj x) ⥤ D
  /-- The w condition of the cocone as an isomorphism-/
  iso : { x y : A} → (f : x ⟶ y) → (I.map f).toFunctor ⋙ i y ≅ i x
  /-- The compatibility condition over iso 𝟙 _ : it equals the isomorphism induced by equality between (I.map (𝟙 _) ⋙ (G a) and  (G a)-/
  isoId : (x  : A) → (iso (𝟙 x)) = eqToIso (by simp [Functor.id_comp])
  /-- The compatibility condition over iso(f ≫ g): it equals the isomorphism induced by equality F.map (f ≫ g) = F.map f ≫ F.map g )-/
  isoComp : {x y z: A } → (f : x ⟶ y) → (g : y ⟶ z) → iso (f ≫ g) = isoWhiskerRight (eqToIso ((Cat.ext_iff.mp (I.map_comp _ _)).trans (Cat.Hom.comp_toFunctor _ _))) (i z) ≪≫ associator (I.map f).toFunctor (I.map g).toFunctor (i z) ≪≫ isoWhiskerLeft (I.map f).toFunctor (iso g) ≪≫ iso f

set_option backward.isDefEq.respectTransparency false in
def truc (t :test I) : CoconeFunctor t.pt I where
  i x := (t.ι.app ⟨x⟩).toFunctor
  iso f := by
    let h := t.ι.naturality ⟨f⟩

    simp only [toPseudofunctor'_obj, const_obj_obj, toPseudofunctor'_map, const_obj_map,
      Category.comp_id] at h


    let h := t.ι.naturality_naturality (eqToHom rfl :⟨f⟩ ⟶ ⟨f⟩ )
    simp at h
    --ça c'est trivial du coup
    simp
    sorry
  isoId x := by
    let h := t.ι.naturality_id ⟨x⟩
    simp at h



    sorry
  isoComp f g:= by
    let h := t.ι.naturality_comp ⟨f⟩ ⟨g⟩
    simp at h


    sorry

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
