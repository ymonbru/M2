import M2.Ksheaves

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite

universe u v w

variable {X : Type w} [TopologicalSpace X]
variable {C : Type u} [Category.{v, u} C] [HasColimitsOfSize.{w, w} C]
variable (p : X)

noncomputable section

variable (F : (Compacts X)ᵒᵖ ⥤ C)

/-- The property of containing p-/
@[simp]
def pinK : Set (Compacts X) := fun K => (p ∈ K)

/-- the induced category by the property pinK-/
def pinK_cat : Type w := ObjectProperty.FullSubcategory (pinK p)

instance : Category (pinK_cat p) := ObjectProperty.FullSubcategory.category (pinK p)

/-- The diagram obtaind by considering F on the previous category-/
@[simps!]
def Fres : (pinK_cat p)ᵒᵖ ⥤ C := (ObjectProperty.ι (pinK p)).op.comp F

/-- The functor that send a K-presheaf to it's stalk in p-/
@[simps]
def KstalkFunctor : ((Compacts X)ᵒᵖ ⥤ C) ⥤ C where
  obj _ := colimit (Fres p _)
  map _ := colimMap <| NatTrans.hcomp (NatTrans.id _) (by assumption)

/--The compact subset of X, induced by the singleton p (because X is Hausdorff)-/
@[simps]
def pC : Compacts X := ⟨{p}, isCompact_singleton⟩

/-- The natural transformation that allows to define F(p) as a cocone of the diagram FUbar-/
@[simps]
def Fp_transNat : (Fres p F) ⟶ ((Functor.const _ ).obj <| op <| pC p).comp F where
app W:= F.map <| op <| homOfLE <| by
  intro _ hx
  rw [ Set.eq_of_mem_singleton hx]
  exact W.unop.property

naturality  _ _ _:= by
  suffices _ = F.map _ by simpa
  rw [← F.map_comp]
  rfl

/-- The cocone of the diagram Fres, with point F(p) and the canonical maps-/
@[simps]
def Fp : Cocone (Fres p F) := Cocone.mk _ <| Fp_transNat _ _  ≫ (Functor.constComp _ _ _).hom

variable (C)

#check pC p
/--The functor that evaluate K-présheaves in {p}-/
@[simps]
def EvalInP : ((Compacts X)ᵒᵖ ⥤ C ) ⥤ C where
  obj _ := (Fp p _ ).pt
  map τ := τ.app <| op (pC p)

/-- The compact subset {p} as a compact subset that contains p-/
@[simps]
def pC2 : (pinK_cat p) := ⟨pC p,rfl⟩

/-- The induced morphism from pC2 to any compact of pinK-/
@[simps!]
def PsubOfpinK (K:pinK_cat p) : (pC2 p) ⟶ K :=  homOfLE ( by
  intro _ h
  rw [h]
  exact K.property)

/-- The evidence that the cocone (Fp p F) is a colimit cocone -/
@[simps]
def FpisCol : IsColimit (Fp p F) where
  desc s :=  s.ι.app <| op (pC2 _)
  fac s K :=  by
    suffices (Fres _ _).map _ ≫ s.ι.app _ =
  s.ι.app _ ≫ ((Functor.const _ ).obj _ ).map (op (PsubOfpinK p K.unop )) by simpa
    apply s.ι.naturality
  uniq s m hm := by
    rw [← hm (op _ )]
    suffices (Fp _ _).ι.app (op (pC2 p)) = 𝟙 _ by
      rw [this]
      simp
    suffices F.map _ = 𝟙 (F.obj _) by simpa
    rw [← F.map_id]
    rfl

/--The cone morphism from the stalk at p tp the cone with point F(p)-/
@[simps]
def StalkToP : (colimit.cocone _ ) ⟶ (Fp p F) where
  hom := colimit.desc _ _

instance IsIsoStalkToP : IsIso (StalkToP C p F) := IsColimit.hom_isIso ( colimit.isColimit _ ) (FpisCol _ _ _ ) _

/-- The canonical natural transformation from the stalk functor to the functor evaluation in p-/
@[simps]
def StalkToPFunc : (KstalkFunctor p ) ⟶ (EvalInP C p )  where
  app _ :=  (StalkToP C p _ ).hom

instance : IsIso (StalkToPFunc C p):= by
  apply ( NatTrans.isIso_iff_isIso_app _).2
  intro _
  rcases (IsIsoStalkToP C p _).out with ⟨i,hi⟩
  use i.hom
  unfold StalkToPFunc
  constructor
  · rw [← Cocone.category_comp_hom, hi.1]
    rfl
  · rw [← Cocone.category_comp_hom, hi.2]
    rfl

/--The isomorphism of functor between taking the stalks and evaluating in p for K-preshaves-/
def IsoKstalkEvalP : (KstalkFunctor p) ≅ (EvalInP C p ) := asIso (StalkToPFunc C p)

variable [T2Space X]

/-- The Kstalk Functor on Ksheaves -/
--@[simps!]
def KstalkFunctorSh : (Ksheaf X C) ⥤ C := (inducedFunctor fun (F : Ksheaf X C) ↦ F.carrier ).comp (KstalkFunctor p)

/-- The EvalInP functor on Ksheaves -/
--@[simps!]
def EvalInPSh : (Ksheaf X C) ⥤ C:= (inducedFunctor fun (F : Ksheaf X C) ↦ F.carrier ).comp (EvalInP C p)

/--The isomorphism of functor between taking the stalks and evaluating in p for Kshaves-/
def IsoKstalkEvalPSh : (KstalkFunctorSh C p) ≅ (EvalInPSh C p ) := isoWhiskerLeft _ (IsoKstalkEvalP C p)

end

#lint
