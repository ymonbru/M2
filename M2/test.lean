import Mathlib
import M2.KsubU
import M2.alpha

open CategoryTheory Limits TopologicalSpace Compacts Opposite Functor TopCat

universe u1 u2 u3 u4 v1 v2 v3 v4

variable {A : Type u1} [Category.{v1, u1} A] {C : Type u2} [Category.{v2, u2} C] {D : Type u3} [Category.{v3, u3} D]

variable {i : A ⥤ Cat.{v4, u4}} (iaSubC : (a : A) → (i.obj a) ⥤ C) (Fia : (a : A) → (i.obj a) ⥤ D) (FcupIa : C ⥤ D)


variable (h1 : (a : A) → (iaSubC a) ⋙ (FcupIa) = (Fia a))
variable (h2 : {a b : A} → (f : a ⟶ b) → (i.map f) ⋙ (iaSubC b) = (iaSubC a))
variable (h3 : {a b : A} → (f : a ⟶ b) → (i.map f) ⋙ (Fia b) = (Fia a)) -- conséquence des deux autres mais on verra plus tard

@[simps!]
def FIaNaturalityIso {a b : A} (f: a ⟶ b) : i.map f ⋙ Fia b ≅ Fia a := eqToIso (h3 f)

variable (a : A)

variable [(a : A) → HasLimitsOfSize.{v3, u3} (i.obj a)]


noncomputable section

variable [HasLimitsOfSize.{v2, u2} D] [HasLimitsOfSize.{v4, u4} D]

#check limit (FcupIa )


noncomputable section
-- pas sur du op mais ça à l'air de marcher mieux
@[simps]
def limFIa : Aᵒᵖ ⥤ D where
  obj a := limit (Fia a.unop)
  map f := (limit.pre (Fia _) (i.map f.unop)) ≫ ((HasLimit.isoOfNatIso (FIaNaturalityIso Fia h3 f.unop)).hom )
  map_comp f g := by
    apply limit.hom_ext
    intro j
    suffices limit.π (Fia (unop _)) ((i.map (g.unop ≫ f.unop)).obj j) ≫ eqToHom _ = limit.π (Fia (unop _)) ((i.map f.unop).obj ((i.map g.unop).obj j)) ≫ eqToHom _ by simpa

    have : ((i.map (g.unop ≫ f.unop)).obj j) = ((i.map f.unop).obj ((i.map g.unop).obj j)) := by
      rw [i.map_comp]
      rfl

    rw [← Limits.limit.π_comp_eqToHom (Fia (unop _ )) this, Category.assoc]
    apply whisker_eq
    apply Eq.symm
    apply eqToHom_trans

variable [HasLimitsOfSize.{v1, u1} D]

#check limit (limFIa Fia h3)

/-- The natural transformation involved in limLimFIaConeFcupIa-/
@[simps]
def limLimFIaConeFcupIaπ : (const C).obj (limit (limFIa Fia h3)) ⟶ FcupIa where
  app x := by
    have x1 : A := sorry
    have x2 : (i.obj x1) := sorry
    have : (iaSubC x1).obj x2 = x := by sorry
    apply limit.π (limFIa Fia h3) (op x1) ≫ _
    simp
    apply _ ≫ (limit.π (FcupIa ) x)

    sorry
    --exact limit.π (limFIa Fia h3) (op x1) ≫ ( limit.π (FcupIa ) x)
  naturality x y f:= by
    rcases f with ⟨f⟩
    suffices limit.π (limFIa i F) _ ≫ limit.π _ _ =
  limit.π _ _ ≫ _ ≫ _ by simpa
    exact whisker_eq _ (Eq.symm (limit.w (FIa i F _) f))

/-- The structure of cone over FCupIa on the limit of limit of FIa's-/
@[simps]
def limLimFIaConeFcupIa : Cone (FCupIa i F) where
  pt := limit (limFIa i F)
  π := limLimFIaConeFcupIaπ i F

@[simps]
def truc3π (s : Cone (FCupIa i F)) : (const ↑(i.obj a)).obj s.pt ⟶ FIa i F a where
  app x := s.π.app ((Sigma.incl a).obj x )
  naturality _ _ f:= by
    beta_reduce
    exact s.π.naturality (((Sigma.incl a)).map f)

@[simps]
def truc3 (s : Cone (FCupIa i F)) : Cone (FIa i F a) where
  pt := s.pt
  π := truc3π i F a s

@[simps]
def truc2π (s : Cone (FCupIa i F)) : (const Aᵒᵖ).obj s.pt ⟶ limFIa i F where
  app a := limit.lift _ (truc3 i F a.unop s)
  naturality a b f:= by
    apply limit.hom_ext
    intro j
    beta_reduce

    simp
    #check (i.map f.unop)
    #check s.π.naturality
    apply eq_of_heq
    apply (heq_comp_eqToHom_iff _ _ _).mpr



    --apply limit.uniq
    sorry



@[simps]
def truc2 (s : Cone (FCupIa i F)) : Cone (limFIa i F) where
  pt := s.pt
  π := truc2π i F s

def truc : IsLimit (limLimFIaConeFcupIa i F) where
  lift s := limit.lift _ (truc2 i F s)
  uniq s (m : s.pt ⟶ limit (limFIa i F)) hm:= by
    apply limit.hom_ext
    intro
    suffices m ≫ limit.π _ _ = limit.lift _ (truc3 i F _ s) by simpa
    apply limit.hom_ext
    intro
    suffices m ≫ limit.π _ _ ≫ limit.π _ _ = s.π.app ⟨_, _⟩ by simpa
    rw [← hm _]
    rfl



end

section -- pour avoir au moins une situation ou ce qui précède s'applique

variable {X : Type u2} [TopologicalSpace X] [T2Space X] (K : Compacts X)
variable {C : Type u2} [Category.{u2, u2} C] (F : (Opens X)ᵒᵖ ⥤ C)

/-@[simps]
def L1subL2supsup { L1 L2 : Compacts X} (f: L1 ⟶ L2) : (supSupK_cat L2 ) ⥤ (supSupK_cat L1) where
  obj M := ⟨M.obj, by
    rcases M.property with ⟨V,hV1,hV2⟩
    use V
    constructor
    apply le_trans
    exact (leOfHom f)
    repeat assumption⟩
  map _ := homOfLE (leOfHom _)


@[simps]
def iEx : (supSupK_cat K)ᵒᵖ  ⥤ Cat where
  obj L := Cat.of (supSupK_cat L.unop.obj)
  map f := L1subL2supsup ((fullSubcategoryInclusion _ ).map f.unop)-/

@[simps]
def iEx : (supSupK_cat K)ᵒᵖ  ⥤ Cat where
  obj L := Cat.of (KsubU_cat L.unop.obj trueCond)ᵒᵖ
  map f := Functor.op (K1subK2subU _ ((fullSubcategoryInclusion _ ).map f.unop))

def FEx : Cocone (iEx K) where
  pt := Cat.of C -- ça impose beaucoup de structure sur l'univers de C -> probablement à refaire
  ι := ⟨fun L => FU L.unop.obj F trueCond, by aesop⟩
