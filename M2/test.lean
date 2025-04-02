import Mathlib
import M2.KsubU
import M2.alpha

open CategoryTheory Limits TopologicalSpace Compacts Opposite Functor TopCat

universe u1 u2 u3 v1 v2 v3

variable {A : Type u2} [Category.{v2, u2} A]

variable (i : A ⥤ Cat.{v3, u3}) [HasColimit i] (F : Cocone i) (a : A)

variable [(a : A) → HasLimitsOfSize.{v3, u3} (i.obj a)]

#check colimit i

noncomputable section

def cupIa : Type u3 := (colimit i).α

instance : Category (cupIa i) := Cat.str _

def FIa : (i.obj a) ⥤ F.pt := F.ι.app a -- pour permetre d'inferer l'existence de limites

#check F.pt

def FCupIa : (cupIa i) ⥤ F.pt := colimit.desc i F

--Sigma.desc (fun a => FIa i F a)--CategoryTheory.Sigma.desc F.ι.app

--#check

variable [HasLimitsOfSize.{v3,u3} F.pt]

#check limit (FCupIa i F)

def Ia : Type u3 := (i.obj a).α

instance : Category (Ia i a) := Cat.str _

variable [HasLimitsOfSize.{v3, u3} F.pt]

@[simps!]
def FIaNaturalityIso {a b : A} (f: a ⟶ b) : i.map f ⋙ FIa i F b ≅ FIa i F a := eqToIso ( by
  have : i.map f ⋙ FIa i F b = i.map f ≫ F.ι.app b := by rfl
  rw [this, F.ι.naturality f]
  rfl)

noncomputable section
-- pas sur du op mais ça à l'air de marcher mieux
@[simps]
def limFIa : Aᵒᵖ ⥤ F.pt where
  obj a := limit (FIa i F a.unop)
  map f := (limit.pre (FIa i F _) (i.map f.unop)) ≫ ((HasLimit.isoOfNatIso (FIaNaturalityIso i F f.unop)).hom )
  map_comp f g := by
    apply limit.hom_ext
    intro j
    suffices limit.π (FIa i F (unop _)) ((i.map (g.unop ≫ f.unop)).obj j) ≫ eqToHom _ =
  limit.π (FIa i F (unop _)) ((i.map f.unop).obj ((i.map g.unop).obj j)) ≫ eqToHom _ by simpa

    have : ((i.map (g.unop ≫ f.unop)).obj j) = ((i.map f.unop).obj ((i.map g.unop).obj j)) := by
      rw [i.map_comp]
      rfl

    rw [← Limits.limit.π_comp_eqToHom (FIa i F (unop _ )) this, Category.assoc]
    apply whisker_eq
    apply Eq.symm
    apply eqToHom_trans


    /-exact
      Eq.symm
        (eqToHom_trans (this ▸ Eq.refl ((FIa i F (unop _)).obj ((i.map (g.unop ≫ f.unop)).obj j)))
          (Eq.trans (congr_obj (FIaNaturalityIso.proof_1 i F f.unop) ((i.map g.unop).obj j))
            (congr_obj (FIaNaturalityIso.proof_1 i F g.unop) j)))


    apply eq_of_heq
    apply heq_comp
    · rfl
    · rw [i.map_comp]
      rfl
    · rfl
    · apply congr_arg_heq
      rw [i.map_comp]
      rfl
    · apply HEq.trans
      apply eqToHom_heq_id_cod
      apply HEq.symm
      apply eqToHom_heq_id_cod
    --show_term (simp [i.map_comp]; congr; simp )
    -- ça 'est vraiment pas beau...-/

variable [HasLimitsOfSize.{v2, u2} F.pt]

#check limit (limFIa i F)

/-- The natural transformation involved in limLimFIaConeFcupIa-/
@[simps]
def limLimFIaConeFcupIaπ : (const (cupIa i)).obj (limit (limFIa i F)) ⟶ FCupIa i F where
  app x := by
    simp
    unfold FCupIa
    #check F.ι
    #check limit.π (limFIa i F)

    sorry



  --limit.π (limFIa i F) (op x.1) ≫ ( limit.π (FIa i F x.1) x.2)
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
