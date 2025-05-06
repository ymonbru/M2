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
-- B n'est pas dans la structure pour eviter des soucis par la suite
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

variable (h : IsColimitF i C iaSubC)

lemma bidule : FcupIa = @h.desc _ _ (Cat.of D) (F iaSubC FcupIa)  := by
  apply @h.uniq  _ _ (Cat.of D) (F iaSubC FcupIa)
  intro a
  simp [F]

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


variable (repO : (x : C) → repObj iaSubC x)
variable (repH : {x y : C} → ( f: x ⟶ y) → repHom iaSubC f)
--def repAHom (x y : C) : A := repA<| IsFiltered.max x y

variable (repCompat : (x : C) → (r1 r2 : repObj iaSubC x) → ∃ g : r1.a ⟶ r2.a, (i.map g).obj r1.ia = r2.ia ∨ ∃ g : r2.a ⟶ r1.a, (i.map g).obj r2.ia = r1.ia )

@[simps]
def repHtoD {x y : C} (f : x ⟶ y) (r : repHom iaSubC f) : (repObj iaSubC x) := ⟨r.a,r.iaDom,r.repDom⟩

@[simps]
def repHtoCd {x y : C} (f : x ⟶ y) (r : repHom iaSubC f) : (repObj iaSubC y) := ⟨r.a,r.iaCoDom,r.repCoDom⟩

@[simps]
def repCanO (a : A) (x : i.obj a) : repObj iaSubC ((iaSubC.i a).obj x) where
  a := a
  ia := x
  rep := eqToIso rfl


@[simp]
lemma bidule2 {x : C}  (r s : repObj iaSubC x) : limit.π (limFia iaSubC FcupIa ) (op r.a) ≫ limit.π ((F iaSubC FcupIa).i r.a) r.ia ≫ FcupIa.map r.rep.hom = limit.π (limFia iaSubC FcupIa ) (op s.a) ≫ limit.π ((F iaSubC FcupIa).i s.a) s.ia ≫ FcupIa.map s.rep.hom := by
  sorry



/-- The natural transformation involved in limLimFIaConeFcupIa-/
@[simps]
def limLimFiaConeFcupIaπ : (const C).obj (limit (limFia iaSubC FcupIa)) ⟶ FcupIa where
  app x := by
    let xr := repO x

    exact limit.π (limFia iaSubC FcupIa ) (op xr.a) ≫ limit.π ((F iaSubC FcupIa).i xr.a) xr.ia ≫ FcupIa.map xr.rep.hom

    --limit.π (limFia h3) (op (repA x)) ≫ limit.π (Fia (repA x)) (repIa x) ≫ (FiaFacIso h1 (repA x)).inv.app _ ≫ FcupIa.map (repSpec x).hom
  naturality x y f:= by
    let fr := repH f
    rw [bidule2 iaSubC FcupIa (repO y) (repHtoCd iaSubC f fr)]
    rw [bidule2 iaSubC FcupIa (repO x) (repHtoD iaSubC f fr)]

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




    /-rcases f with ⟨f⟩
    suffices limit.π (limFIa i F) _ ≫ limit.π _ _ =
  limit.π _ _ ≫ _ ≫ _ by simpa
    exact whisker_eq _ (Eq.symm (limit.w (FIa i F _) f))-/

/-- The structure of cone over FCupIa on the limit of limit of FIa's-/
@[simps!]
def limLimFiaConeFcupIa : Cone FcupIa where
  pt := limit (limFia iaSubC FcupIa )
  π := limLimFiaConeFcupIaπ iaSubC FcupIa repO repH

@[simps]
def truc3π (s : Cone FcupIa) : (const (i.obj a)).obj s.pt ⟶ (F iaSubC FcupIa).i a where
  app x := s.π.app ((iaSubC.i a).obj x)
  naturality x1 x2 f:= by
    simp [F]

@[simps]
def truc3 (s : Cone FcupIa) : Cone ((F iaSubC FcupIa).i a) where
  pt := s.pt
  π := truc3π iaSubC FcupIa a s

@[simps]
def truc2π (s : Cone FcupIa) : (const Aᵒᵖ).obj s.pt ⟶ limFia iaSubC FcupIa where
  app a := limit.lift _ (truc3 iaSubC FcupIa a.unop s)
  naturality a b f:= by
    apply limit.hom_ext
    intro j
    simp [F]

@[simps]
def truc2 (s : Cone FcupIa ) : Cone (limFia iaSubC FcupIa) where
  pt := s.pt
  π := truc2π iaSubC FcupIa s

def truc : IsLimit (limLimFiaConeFcupIa iaSubC FcupIa repO repH) where
  lift s := limit.lift _ (truc2 iaSubC FcupIa s)
  uniq s (m : s.pt ⟶ limit (limFia iaSubC FcupIa)) hm:= by
    apply limit.hom_ext
    intro a
    apply limit.hom_ext
    intro x
    suffices m ≫ limit.π (limFia iaSubC FcupIa) a ≫ limit.π ((F iaSubC FcupIa).i (unop a)) x = s.π.app ((iaSubC.i (unop a)).obj x) by simpa

    rw [← hm _]

    apply whisker_eq
    have : limit.π (limFia iaSubC FcupIa) a ≫ limit.π ((F iaSubC FcupIa).i (unop a)) x = limit.π (limFia iaSubC FcupIa ) (op (repCanO iaSubC (unop a) x).a) ≫ limit.π ((F iaSubC FcupIa).i (repCanO iaSubC (unop a) x).a) (repCanO iaSubC (unop a) x).ia ≫ FcupIa.map (repCanO iaSubC (unop a) x).rep.hom := by simp [F]

    rw [this, bidule2 iaSubC FcupIa (repCanO iaSubC a.unop x) (repO ((iaSubC.i (unop a)).obj x))]

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
def iaSubCEx (L : (supSupK_cat K)ᵒᵖ ) : ((iEx K ).obj L) ⥤ (KsubU_cat K trueCond)ᵒᵖ  where
  obj U := ⟨U.unop.obj,⟨Set.Subset.trans (supSupKtoSupK K (unop L)) (unop U).property.left, of_eq_true (eq_self true)⟩⟩
  map f := op <| homOfLE <| leOfHom f.unop

def chose : CoconeFunctor (KsubU_cat K trueCond)ᵒᵖ (iEx K) where
  i := iaSubCEx K
  iso _ := eqToIso rfl
  isoId _ := rfl
  isoComp _ _ := rfl

def FcupIaEx  : (KsubU_cat K trueCond)ᵒᵖ ⥤ D := (fullSubcategoryInclusion _ ).op ⋙ F

#check CoconeFWhisker _ (chose K) (FcupIaEx K F)

variable [HasLimitsOfSize.{u1, u1, u2, u2} D]

#check limFia (chose K) (FcupIaEx K F)

variable [LocallyCompactSpace X]

@[simps]
def repAEx (U : (KsubU_cat K trueCond)ᵒᵖ) : (supSupK_cat K)ᵒᵖ := by

  let ⟨L,hL⟩ := Classical.choice (existsIntermed X K U.unop.obj U.unop.property.1)
  apply op
  use ⟨L, hL.1⟩
  use ⟨interior L,@isOpen_interior X L _⟩
  constructor
  exact hL.2.1
  exact interior_subset

@[simps]
def repIaEx (U : (KsubU_cat K trueCond)ᵒᵖ) : ((iEx K).obj (repAEx K U)) := op ⟨U.unop.obj, by
      constructor
      exact (Classical.choice (existsIntermed X K U.unop.obj U.unop.property.1)).2.2.2
      rfl⟩



-- (repSpec : (x : C) → (iaSubC (repA x)).obj (repIa x) ≅ x)
def repSpecEx (U : (KsubU_cat K trueCond)ᵒᵖ) : ((iaSubCEx K (repAEx K U)).obj (repIaEx K U) ≅ U) := eqToIso rfl

@[simps]
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
    apply CategoryTheory.Functor.ext (h_map := ?_)
    sorry


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


#check chose2
