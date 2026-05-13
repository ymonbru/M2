import M2.Propre.Topology
import M2.forceColimW
import Mathlib

open CategoryTheory Limits TopologicalSpace Compacts Opposite Functor Pseudofunctor.StrongTrans

universe u1 u2 u3 u4 v1 v2 v3 v4

@[simps]
def CategoryTheory.Functor.ofCatHom {C D : Cat} : (C ⟶ D) ⥤ (C.1 ⥤ D.1) where
  obj F := F.toFunctor
  map {F G} τ := τ.toNatTrans

#check ofCatHom.mapIso

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

variable {x : Cat.{v1, u1}}
variable [HasColimitsOfSize.{v2, u2, v1, u1} x.1]

instance {F : B ⥤ᵖ Cat.{v1, u1}} (c : Cocone F) ( f : c.pt ⟶ x)  : HasColimitsOfSize.{v2, u2, v1, u1} ((c.extend f).pt).1 := by
  simp only [Cocone.extend_pt]
  assumption

/-def Cocone.whisker {D : Type*} [Bicategory D] (E : D ⥤ᵖ B) (c : Cocone F) : Cocone (E.comp F) where
  pt := c.pt
  ι := by
    --est-ce que j'ai vraiment besoin de ça?
    sorry-/

variable {B : Type u1 } [Category.{v1, u1} B]
variable {I : LocallyDiscrete B ⥤ᵖ Cat.{v2, u2}} (c : Cocone I)

def Cocone.ιF (b : B) : I.obj ⟨b⟩ ⥤ c.pt := (c.ι.app ⟨b⟩).toFunctor

@[simps!]
def Cocone.wF {a b : B} (f : a ⟶ b) : (I.map ⟨f⟩).toFunctor ⋙ c.ιF b ≅ c.ιF a := Functor.ofCatHom.mapIso (c.ι.naturality ⟨f⟩)

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma Cocone.idF (b : B) : c.wF (𝟙 b) = isoWhiskerRight (Functor.ofCatHom.mapIso (I.mapId ⟨b⟩)) (c.ιF b) ≪≫ Functor.leftUnitor (c.ιF b) := by
  ext x
  simpa using funext_iff.1 (NatTrans.ext_iff.1 (Cat.Hom₂.ext_iff.1 (c.ι.naturality_id ⟨b⟩))) x

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma Cocone.compF {a b d : B} (f : a ⟶ b) (g : b ⟶ d) : c.wF (f ≫ g) = (isoWhiskerRight (ofCatHom.mapIso (I.mapComp ⟨f⟩ ⟨g⟩)) (c.ιF d) ≪≫ (I.map ⟨f⟩).toFunctor.isoWhiskerLeft (c.wF g)) ≪≫ c.wF f := by
  ext x
  simpa using funext_iff.1 (NatTrans.ext_iff.1 (Cat.Hom₂.ext_iff.1 (c.ι.naturality_comp ⟨f⟩ ⟨g⟩))) x

/-def Cocone.extendF {D : Type u3} [Category.{v3, u3} D] (F : c.pt ⥤ D) : Cocone I where
  pt := Cat.of D
  ι := sorry-/

set_option backward.isDefEq.respectTransparency false in
@[simps]
def Cocone.fromGrothendieck : I.Grothendieck ⥤ c.pt where
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
    suffices (c.ι.app { as := z.base }).toFunctor.map (f ≫ g).fiber = (c.ι.naturality (f.1.toLoc ≫ g.1.toLoc)).hom.toNatTrans.app x.fiber ≫ ?_ by
      rw [this, ← Category.assoc]
      simp
      rfl
    let h := funext_iff.1 (NatTrans.ext_iff.1 (Cat.Hom₂.ext_iff.1 (c.ι.naturality_comp f.1.toLoc g.1.toLoc))) x.fiber
    simp at h
    rw [h]
    simp

variable {D : Cat.{v2, u2}}
variable (F : c.pt ⟶ D)

#check Bicategory.Cocone.extend c

set_option backward.isDefEq.respectTransparency false in
lemma hey : (c.extend F).fromGrothendieck = c.fromGrothendieck ⋙ F.toFunctor := Functor.ext (by simp) (by simp)

variable [HasColimitsOfSize.{v2, u2} c.pt]

set_option backward.isDefEq.respectTransparency false in
@[simps]
noncomputable def CoconeFunctor.colim [HasColimitsOfSize.{v2, u2} c.pt] : B ⥤ c.pt where
  obj b := colimit (c.ιF b)
  map {a b} f := (HasColimit.isoOfNatIso (c.wF f).symm).hom ≫ colimit.pre (c.ιF b) (I.map ⟨f⟩).toFunctor
  map_id b := by
    ext x
    simp
    forceColimW
  map_comp {a b d} f g := by
    ext x
    simp
    apply whisker_eq
    apply whisker_eq
    forceColimW

variable [HasColimitsOfSize.{v1, u1} c.pt] [HasColimitsOfSize.{max v1 v2, max u1 u2} c.pt]

set_option backward.isDefEq.respectTransparency false in
@[simps]
noncomputable def bidule : Limits.Cocone (Cocone.fromGrothendieck c) where
  pt := colimit (CoconeFunctor.colim c)
  ι.app x := colimit.ι (c.ιF x.1) x.2 ≫ colimit.ι (CoconeFunctor.colim c) x.1
  ι.naturality {x y } f := by
    rw [← colimit.w (CoconeFunctor.colim c) f.1]
    simp
    let h : ?_ = colimit.ι (c.ιF y.base) ((I.map { as := f.base }).toFunctor.obj x.fiber) := by exact colimit.w (c.ιF y.base) f.2
    rw [← h]
    simp [Cocone.ιF];rfl

set_option backward.isDefEq.respectTransparency false in
@[simps]
def machin (s : Limits.Cocone (Cocone.fromGrothendieck c)) (b : B) : Limits.Cocone (c.ιF b) where
  pt := s.pt
  ι.app x := s.ι.app ⟨b,x⟩
  ι.naturality x y f:= by
    have : ?_ = s.ι.app { base := b, fiber := x } := by simpa using s.ι.naturality (⟨𝟙 _, ((I.mapId ⟨b⟩).hom).toNatTrans.app x ≫ f⟩ : (⟨b,x⟩ : I.Grothendieck) ⟶ ⟨b,y⟩)
    rw [← this]
    suffices (c.ι.naturality (𝟙 { as := b })).hom.toNatTrans.app x = (c.ι.app { as := b }).toFunctor.map ((I.mapId { as := b }).hom.toNatTrans.app x) by
      rw [← this]
      simp;rfl
    simpa using funext_iff.1 (NatTrans.ext_iff.1 ( Cat.Hom₂.ext_iff.1 (c.ι.naturality_id ⟨b⟩))) x

set_option backward.isDefEq.respectTransparency false in
@[simps]
noncomputable def machin2 (s : Limits.Cocone (Cocone.fromGrothendieck c)) : Limits.Cocone (CoconeFunctor.colim c) where
  pt := s.pt
  ι.app b := colimit.desc _ (machin c s b)
  ι.naturality {a b} f := by
    apply colimit.hom_ext
    intro x
    simpa using (s.w (⟨f, eqToHom rfl⟩ : (⟨a, x⟩ : I.Grothendieck) ⟶ ⟨b, (I.map { as := f }).toFunctor.obj x ⟩))

set_option backward.isDefEq.respectTransparency false in
noncomputable def biduleColimit : IsColimit (bidule c) where
  desc s := colimit.desc _ (machin2 c s)
  uniq s m hm := by
    apply colimit.hom_ext (F := (CoconeFunctor.colim c))
    intro b
    apply colimit.hom_ext
    intro x
    simpa using hm ⟨b,x⟩

noncomputable def truc : colimit (CoconeFunctor.colim c) ≅ colimit (Cocone.fromGrothendieck c) := Limits.IsColimit.coconePointUniqueUpToIso (biduleColimit c) (Limits.colimit.isColimit _)

variable [c.fromGrothendieck.Final]
variable [HasColimitsOfSize.{v2, u2} D]
variable [HasColimitsOfSize.{v2, u2} (c.extend F).pt]
variable [HasColimitsOfSize.{v1, u1} (c.extend F).pt]
variable [HasColimitsOfSize.{max v2 v1, max u2 u1} (c.extend F).pt]

noncomputable def cool := truc (c.extend F) ≪≫ Limits.HasColimit.isoOfNatIso (eqToIso (hey c F)) ≪≫ Functor.Final.colimitIso c.fromGrothendieck F.toFunctor

end CategoryTheory.Bicategory

noncomputable section

variable {X : Type u1} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X](K : Compacts X)
variable {D : Type u1} [Category.{u1, u1} D] (F : (Opens X)ᵒᵖ ⥤ D)
-- oblige à travailler avec D sur l'univers u1, est-ce que c'est mal???

variable [HasColimitsOfSize.{u1, u1} D]

def iEx : (K.compactNhds )ᵒᵖ ⥤ Cat where
  obj L := Cat.of (L.unop.val.openNhds)ᵒᵖ
  map {L M} i := ⟨(monoBaseChangeOpenNhds i.1).functor.op⟩

def IEx := (iEx K ).toPseudofunctor'

@[simps]
def cEx : Bicategory.Cocone (IEx K) where
  pt := Cat.of (K.openNhds)ᵒᵖ
  ι.app L := ⟨(monoBaseChangeOpenNhds (homOfLE (subset_of_mem_compactNhds ( Subtype.coe_prop L.as.unop)))).functor.op⟩
  ι.naturality i := eqToIso rfl

instance : IsFilteredOrEmpty (IEx K).Grothendieck where
  cocone_objs d1 d2 := by
    use ⟨op (d1.1.unop ⊓ d2.1.unop), op ⟨d1.2.unop ⊓ d2.2.unop,by dsimp [openNhds]; exact inf_le_inf d1.2.unop.2 d2.2.unop.2⟩⟩
    use ⟨op (homOfLE inf_le_left), op (homOfLE (by simp [IEx, iEx, baseChangeOpenNhds]; exact inf_le_left))⟩
    use ⟨op (homOfLE inf_le_right), op (homOfLE (by simp [IEx,iEx,baseChangeOpenNhds]; exact inf_le_right))⟩
  cocone_maps _ x _ _ := by
    use x
    use 𝟙 _
    rfl

instance : (cEx K).fromGrothendieck.Final := by
  rw [Functor.final_iff_of_isFiltered]
  constructor
  · intro d
    obtain ⟨L,hL⟩ := exists_compact_between  K.isCompact' (Opens.isOpen _) (d.unop.2)
    use ⟨ op (compactNhds_of_existsOpenSubsetBetween ⟨L,hL.1⟩ ⟨interior L,isOpen_interior⟩ hL.2.1 interior_subset), op ⟨d.unop.1, hL.2.2⟩⟩
    apply Nonempty.intro
    exact op (homOfLE (by simp [baseChangeOpenNhds]))
  · intro _ x _ _
    use x
    use 𝟙 _
    rfl

#check Bicategory.cool (cEx K) (by
  simp [cEx]
  sorry)

#check (ObjectProperty.ι (K.openNhds) ).op ⋙ F

variable [HasColimitsOfSize.{u1, u1, u1, u1} ↑(Cat.of D)]

#check Bicategory.cool (cEx K) (D := Cat.of D) ⟨(Subtype.mono_coe _).functor.op ⋙ F⟩

example : 1 = 1 := by
  let h := Bicategory.cool (cEx K) (D := Cat.of D) ⟨(Subtype.mono_coe _).functor.op ⋙ F⟩
  simp at h
  sorry
end

namespace CategoryTheory.Limits.UnionCat
open Bicategory

variable {A : Type u1} [Category.{v1, u1} A] {D : Type u3} [Category.{v3, u3} D]

variable {I : LocallyDiscrete A ⥤ᵖ Cat.{v2, u2}}

variable (D I) in
/-- The data of a Cocone for F, but with isomorphism instead of equality and the lemmas that allow computation

D is not part of the structure to avoid issue in inferance later-/
structure CoconeF where
  /-- the canonial morphisms of the cocone-/
  ι : (x : A) → (I.obj ⟨x⟩) ⥤ D
  /-- The w condition of the cocone as an isomorphism-/
  w : { x y : A} → (f : x ⟶ y) → (I.map ⟨f⟩).toFunctor ⋙ ι y ≅ ι x
  /-- The compatibility condition over iso 𝟙 _ : it equals the isomorphism induced by equality between (I.map (𝟙 _) ⋙ (G a) and  (G a)-/
  wId (x : A) : w (𝟙 x) = isoWhiskerRight (Functor.ofCatHom.mapIso (I.mapId ⟨x⟩)) (ι x) ≪≫ Functor.leftUnitor (ι x)
  /-- The compatibility condition over iso(f ≫ g): it equals the isomorphism induced by equality F.map (f ≫ g) = F.map f ≫ F.map g )-/
  wComp {x y z : A } (f : x ⟶ y) (g : y ⟶ z) : w (f ≫ g) = (isoWhiskerRight (ofCatHom.mapIso (I.mapComp ⟨f⟩ ⟨g⟩)) (ι z) ≪≫ (I.map ⟨f⟩).toFunctor.isoWhiskerLeft (w g)) ≪≫ w f

variable {C : Type u4} [Category.{v4, u4} C] (sD : CoconeF D I)

set_option backward.isDefEq.respectTransparency false in
/-- Build a new CoconeFunctor by whiskering the data to the right-/
@[simps]
def  CoconeF.extend (H : D ⥤ C) : CoconeF C I where
ι x := sD.ι x ⋙ H
w f := (I.map ⟨f⟩).toFunctor.associator  (sD.ι _) H ≪≫ (isoWhiskerRight (sD.w f) H)
wId x := by
  ext
  simp [sD.wId x]
  exact Category.id_comp _
wComp {x y z} f g := by
  ext
  simp [sD.wComp f g]
  exact Category.id_comp _

set_option backward.isDefEq.respectTransparency false in
@[simps]
noncomputable def CoconeF.colim [HasColimitsOfSize.{v2, u2} D] : A ⥤ D where
  obj x := colimit (sD.ι x)
  map {x y} f := (HasColimit.isoOfNatIso (sD.w f).symm).hom ≫ colimit.pre (sD.ι y) (I.map ⟨f⟩).toFunctor
  map_id x := by
    ext
    simp [sD.wId]
    forceColimW
  map_comp {a b d} f g := by
    ext x
    simp [sD.wComp]
    forceColimW

set_option backward.isDefEq.respectTransparency false in
@[simps]
def CoconeF.fromGrothendieck : I.Grothendieck ⥤ D where
  obj g := (sD.ι g.1).obj g.2
  map {g h} f := (sD.w f.1).inv.app g.2 ≫ (sD.ι h.1).map f.2
  map_id x := by
    suffices (sD.w _).hom.app x.fiber = (sD.ι x.base).map (𝟙 x : x ⟶ x).fiber by
      rw [← this]
      simp
    simp [sD.wId]
  map_comp {x y z } f g:= by
    suffices (sD.ι z.base).map (f ≫ g).fiber = (sD.w (f ≫ g).base).hom.app x.fiber ≫ ((sD.w f.base).inv.app x.fiber ≫ (sD.ι y.base).map f.fiber) ≫ (sD.w g.base).inv.app y.fiber ≫ (sD.ι z.base).map g.fiber by
      rw [this]
      simp
    simp [sD.wComp];rfl

set_option backward.isDefEq.respectTransparency false in
lemma hey (H : D ⥤ C) : (sD.extend H).fromGrothendieck = sD.fromGrothendieck ⋙ H := Functor.ext (by simp) (by simp)


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
