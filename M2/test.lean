import Mathlib
import M2.KsubU
import M2.RCalpha

open CategoryTheory Limits TopologicalSpace Compacts Opposite Functor TopCat

universe u1 u2 u3 u4 v1 v2 v3 v4

variable {A : Type u1} [Category.{v1, u1} A] {C : Type u2} [Category.{v2, u2} C] {D : Type u3} [Category.{v3, u3} D]

variable {i : A ⥤ Cat.{v4, u4}} (iaSubC : (a : A) → (i.obj a) ⥤ C) (FcupIa : C ⥤ D) (a : A)


def Fia (a : A) : (i.obj a) ⥤ D := (iaSubC a) ⋙ (FcupIa)

def h1 (a : A) : (iaSubC a) ⋙ (FcupIa) ≅ (Fia iaSubC FcupIa a) := eqToIso rfl

variable (h2 : {a b : A} → (f : a ⟶ b) → (i.map f) ⋙ (iaSubC b) ≅ (iaSubC a))


variable (h3 : {a b : A} → (f : a ⟶ b) → (i.map f) ⋙ (Fia iaSubC FcupIa b) ≅ (Fia iaSubC FcupIa a)) -- conséquence des deux autres mais on verra plus tard,
/-
@[simps!]
def h3bis {a b : A} (f : a ⟶ b) : (i.map f) ⋙ (Fia b) ≅ (Fia a) := (isoWhiskerLeft _ (h1 b).symm).trans <| (associator _ _ _ ).symm.trans <|(isoWhiskerRight (h2 f) _).trans (h1 a)-/

--variable (h3id : (a  : A) → (h3 𝟙 _) = Iso.refl (Fia a))
--variable (h3comp : {a b c : A} → (f : a ⟶ b) → (g : b ⟶ c) → (h3 (f ≫ g) = Iso.trans (isoWhiskerLeft f (h3 g)) (h3 f) ))

#check i.map (𝟙 _) ⋙ (Fia iaSubC FcupIa a)

@[simps!]
def FiaIdIso (a : A) : (i.map (𝟙 _) ⋙ (Fia iaSubC FcupIa a) ≅ (Fia iaSubC FcupIa a)) := eqToIso (by
  apply CategoryTheory.Functor.ext
  intro b c f
  apply eq_of_heq
  apply (heq_eqToHom_comp_iff _ _ _).2
  apply (heq_comp_eqToHom_iff _ _ _).2
    --refine HEq.symm (hcongr_hom ?_ f)
  congr
  · simp [i.map_id]
    rfl
  · simp)

variable (h3id : (a  : A) → (h3 (𝟙 a)) = FiaIdIso iaSubC FcupIa a)

variable {a b c : A } (f : a ⟶ b) (g :b ⟶ c)
--#check (h3 (i.map (f ≫ g)))

@[simps!]
def imapCompFiaIso {a b c : A } (f : a ⟶ b) (g :b ⟶ c) : i.map (f ≫ g) ⋙ Fia iaSubC FcupIa c ≅ Fia iaSubC FcupIa a := isoWhiskerRight (eqToIso (i.map_comp _ _)) (Fia iaSubC FcupIa c) ≪≫ associator (i.map f) (i.map g) (Fia iaSubC FcupIa c) ≪≫ isoWhiskerLeft (i.map f) (h3 g) ≪≫ h3 f


variable (h3comp : {a b c : A } → (f : a ⟶ b) → (g :b ⟶ c) → (h3 (f ≫ g) = imapCompFiaIso iaSubC FcupIa h3 f g))
/-
@[simps!]
def FiaNaturalityIso {a b : A} (f: a ⟶ b) : i.map f ⋙ Fia b ≅ Fia a := eqToIso (h3 f)

@[simps!]
def FiaFacIso (a : A) : (iaSubC a) ⋙ (FcupIa) ≅ (Fia a) := eqToIso (h1 a)-/

variable (a : A)

variable [(a : A) → HasLimitsOfSize.{v3, u3} (i.obj a)]


noncomputable section

variable [HasLimitsOfSize.{v2, u2} D] [HasLimitsOfSize.{v4, u4} D]

#check limit (FcupIa )


noncomputable section
-- pas sur du op mais ça à l'air de marcher mieux
@[simps]
def limFia : Aᵒᵖ ⥤ D where
  obj a := limit (Fia iaSubC FcupIa a.unop)
  map f := (limit.pre (Fia iaSubC FcupIa _) (i.map f.unop)) ≫ ((HasLimit.isoOfNatIso (h3 f.unop)).hom )
  map_id a := by
    ext
    rw [unop_id, Category.assoc, HasLimit.isoOfNatIso_hom_π, h3id]
    simp
  map_comp f g := by
    ext
    suffices limit.π _ _ ≫ _ = limit.π _ _ ≫ _ by simpa
    rw [h3comp]
    simp

variable [HasLimitsOfSize.{v1, u1} D]

#check limit (limFia iaSubC FcupIa h3 h3id h3comp)

variable {repA : C → A} {repIa : (x : C) → i.obj (repA x)} (repSpec : (x : C) → (iaSubC (repA x)).obj (repIa x) ≅ x)


/-- The natural transformation involved in limLimFIaConeFcupIa-/
@[simps]
def limLimFiaConeFcupIaπ : (const C).obj (limit (limFia iaSubC FcupIa h3 h3id h3comp)) ⟶ FcupIa where
  app x := limit.π (limFia iaSubC FcupIa h3 h3id h3comp) (op (repA x)) ≫ limit.π (Fia iaSubC FcupIa (repA x)) (repIa x) ≫ FcupIa.map (repSpec x).hom
    --limit.π (limFia h3) (op (repA x)) ≫ limit.π (Fia (repA x)) (repIa x) ≫ (FiaFacIso h1 (repA x)).inv.app _ ≫ FcupIa.map (repSpec x).hom
  naturality x y f:= by
    simp

    sorry
    /-rcases f with ⟨f⟩
    suffices limit.π (limFIa i F) _ ≫ limit.π _ _ =
  limit.π _ _ ≫ _ ≫ _ by simpa
    exact whisker_eq _ (Eq.symm (limit.w (FIa i F _) f))-/

/-- The structure of cone over FCupIa on the limit of limit of FIa's-/
@[simps!]
def limLimFiaConeFcupIa : Cone FcupIa where
  pt := limit (limFia iaSubC FcupIa h3 h3id h3comp)
  π := limLimFiaConeFcupIaπ h1 h3 repSpec

@[simps]
def truc3π (s : Cone FcupIa) : (const ↑(i.obj a)).obj s.pt ⟶ Fia a where
  app x := s.π.app ((iaSubC a).obj x) ≫ (FiaFacIso h1 a).hom.app x
  naturality x1 x2 f:= by
    have : s.π.app ((iaSubC a).obj x2) =
  s.π.app ((iaSubC a).obj x1) ≫ FcupIa.map ((iaSubC a).map f) := by
      rw [ ← s.π.naturality ((iaSubC a).map f)]
      simp
    rw [this, Category.assoc, Category.assoc, Functor.congr_hom (h1 a).symm f]
    simp


@[simps]
def truc3 (s : Cone FcupIa) : Cone (Fia a) where
  pt := s.pt
  π := truc3π h1 a s

@[simps]
def truc2π (s : Cone FcupIa) : (const Aᵒᵖ).obj s.pt ⟶ limFia h3 where
  app a := limit.lift _ (truc3 h1 a.unop s)
  naturality a b f:= by
    apply limit.hom_ext
    intro j
    suffices s.π.app ((iaSubC (unop b)).obj j) ≫ eqToHom _ = s.π.app ((iaSubC (unop a)).obj ((i.map f.unop).obj j)) ≫ eqToHom _ by simpa

    have :(iaSubC (unop b)).obj j = (iaSubC (unop a)).obj ((i.map f.unop).obj j) := by
      rw [← (h2 f.unop)]
      rfl
    congr
    exact heq_of_eqRec_eq (congrFun (congrArg Eq (congrArg FcupIa.obj this)) ((Fia (unop b)).obj j)) rfl

@[simps]
def truc2 (s : Cone FcupIa ) : Cone (limFia h3) where
  pt := s.pt
  π := truc2π h1 h2 h3 s

def truc : IsLimit (limLimFiaConeFcupIa h1 h3 repSpec) where
  lift s := limit.lift _ (truc2 h1 h2 h3 s)
  uniq s (m : s.pt ⟶ limit (limFia h3)) hm:= by
    apply limit.hom_ext
    intro a
    suffices m ≫ limit.π _ _ = limit.lift _ (truc3 h1 _ s) by simpa
    apply limit.hom_ext
    intro x
    suffices m ≫ limit.π _ _ ≫ limit.π _ _ = s.π.app ((iaSubC (unop _)).obj _) ≫ _ by simpa
    rw [← hm _]
    simp
    apply whisker_eq

    sorry



end

noncomputable section -- pour avoir au moins une situation ou ce qui précède s'applique

variable {X : Type u1} [TopologicalSpace X] [T2Space X] (K : Compacts X)
variable {D : Type u2} [Category.{u2, u2} D] (F : (Opens X)ᵒᵖ ⥤ D)

@[simps]
def iEx : (supSupK_cat K)ᵒᵖ  ⥤ Cat where
  obj L := Cat.of (KsubU_cat L.unop.obj trueCond)ᵒᵖ
  map f := Functor.op (K1subK2subU _ ((fullSubcategoryInclusion _ ).map f.unop))

@[simps]
def iaSubCEx (L : (supSupK_cat K)ᵒᵖ ) : ((iEx K ).obj L) ⥤ (KsubU_cat K trueCond)ᵒᵖ  where
  obj U := ⟨U.unop.obj,by
    constructor
    · apply Set.Subset.trans
      apply supSupKtoSupK K L.unop
      exact U.unop.property.1
    · simp⟩
  map f := op <| homOfLE <| leOfHom f.unop

def FiaEx (L : (supSupK_cat K)ᵒᵖ ) : ((iEx K ).obj L) ⥤ D := (fullSubcategoryInclusion _ ).op ⋙ F

def FcupIaEx  : (KsubU_cat K trueCond)ᵒᵖ ⥤ D := (fullSubcategoryInclusion _ ).op ⋙ F

lemma h1Ex (L : (supSupK_cat K)ᵒᵖ ) : (iaSubCEx K L) ⋙ (FcupIaEx K F) = (FiaEx K F L) := by rfl

lemma h2Ex {L1 L2 : (supSupK_cat K)ᵒᵖ } (f : L1 ⟶ L2) : ((iEx K).map f) ⋙ (iaSubCEx K L2) = (iaSubCEx K L1) := by rfl

lemma h3Ex {L1 L2 : (supSupK_cat K)ᵒᵖ } (f : L1 ⟶ L2) : ((iEx K).map f) ⋙ (FiaEx K F L2) = (FiaEx K F L1) := by rfl

variable [HasLimitsOfSize.{u1, u1, u2, u2} D]

#check limFia (iaSubCEx K) (FcupIaEx K F) (fun _ => eqToIso rfl) (fun _ => rfl) (fun _ _ => by ext; simp)

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
def repIaEx (U : (KsubU_cat K trueCond)ᵒᵖ) : ((iEx K).obj (repAEx K U)) := by
  apply op
  use U.unop.obj
  constructor
  exact (Classical.choice (existsIntermed X K U.unop.obj U.unop.property.1)).2.2.2
  rfl

def test { U V :(KsubU_cat K trueCond)ᵒᵖ } (f : U ⟶ V ): (repIaEx K U) ⥤ (repIaEx K V):= by
  sorry


-- (repSpec : (x : C) → (iaSubC (repA x)).obj (repIa x) ≅ x)
def repSpecEx (U : (KsubU_cat K trueCond)ᵒᵖ) : ((iaSubCEx K (repAEx K U)).obj (repIaEx K U) ≅ U) := eqToIso rfl
