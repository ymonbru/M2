import Mathlib
import Mathlib.Topology.Separation
--import M2.Ksheaves

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite

variable {X} [TopologicalSpace X] --[T2Space X]
variable (p : X)
attribute [local aesop safe (rule_sets := [CategoryTheory])] colimit.hom_ext limit.hom_ext

noncomputable section

variable (F : (Compacts X)ᵒᵖ ⥤ Ab)

/-- The property of containing p-/
def pinK : Set (Compacts X) := fun K => (p ∈ K)

/-- the induced category by the property pinK-/
def pinK_cat : Type := FullSubcategory (pinK p)

instance : Category (pinK_cat p) := FullSubcategory.category (pinK p)

/-- The diagram obtaind by considering F on the previous category-/
@[simps!]
def Fres : (pinK_cat p)ᵒᵖ ⥤ Ab := (fullSubcategoryInclusion (pinK p)).op.comp F

/-- The functor that send a K-presheaf to it's stalk in p-/
@[simps]
def KstalkFunctor : ((Compacts X)ᵒᵖ ⥤ Ab) ⥤ Ab where
  obj _ := colimit (Fres p _)
  map _ := colimMap <| NatTrans.hcomp (NatTrans.id _) (by assumption)

/--The compact subset of X, induced by the singleton p (because X is Hausdorff)-/
@[simps?]
def pC : Compacts X := ⟨{p}, isCompact_singleton⟩

/-- The natural transformation that allows to define F(p) as a cocone of the diagram FUbar-/
@[simps]
def Fp_transNat : (Fres p F) ⟶ ((Functor.const _ ).obj <| op <| pC p).comp F where
app W:= F.map <| op <| homOfLE <| by
  intro _ hx
  rw [ Set.eq_of_mem_singleton hx]
  exact W.unop.property

naturality  _ _ _:= by
  suffices F.map _ ≫ F.map _ = F.map _ by simpa
  rw [← F.map_comp]
  rfl

/-- The cocone of the diagram Fres, with point F(p) and the canonical maps-/
@[simps]
def Fp : Cocone (Fres p F) := Cocone.mk _ <| Fp_transNat _ _  ≫ (Functor.constComp _ _ _).hom

#check pC p
/--The functor that evaluate K-présheaves in {p}-/
@[simps]
def EvalInP : ((Compacts X)ᵒᵖ ⥤ Ab ) ⥤ Ab where
  obj _ := (Fp p _ ).pt
  map τ := τ.app <| op (pC p)

/-- The compact subset {p} as a compact subset that contains p-/
@[simps]
def pC2 : (pinK_cat p) := ⟨pC p,rfl⟩

/-- The evidence that the cocone (Fp p F) is a colimit cocone -/
def FpisCol : IsColimit (Fp p F) where
  desc s :=  s.ι.app <| op (pC2 _)
  fac s _ :=  s.ι.naturality _
  uniq s m hm := by
    beta_reduce
    rw [← hm (op _ )]
    suffices (Fp p F).ι.app (op (pC2 p)) = 𝟙 _ by
      rw [this]
      simp
    apply F.map_id


/--The cone morphism from the stalk at p tp the cone with point F(p)-/
@[simps]
def StalkToP : (colimit.cocone _ )⟶ (Fp p F) where
  hom := colimit.desc _ _

instance IsIsoStalkToP : IsIso (StalkToP p F) := IsColimit.hom_isIso ( colimit.isColimit _ ) (FpisCol _ _ ) _


/-- The canonical natural transformation from the stalk functor to the functor evaluation in p-/
@[simps]
def StalkToPFunc : (KstalkFunctor p ) ⟶ (EvalInP p )  where
  app _ :=  (StalkToP p _ ).hom

instance : IsIso (StalkToPFunc p):= by
  apply ( NatTrans.isIso_iff_isIso_app _).2
  intro _
  rcases (IsIsoStalkToP p _).out with ⟨i,hi⟩
  use i.hom

  unfold StalkToPFunc
  constructor
  · rw [← Cocone.category_comp_hom, hi.1]
    rfl
  · rw [← Cocone.category_comp_hom, hi.2]
    rfl

/--The isomorphisme of functor between taking the stalks and evaluating in p for K-preshaves-/
def IsoAlphaUpPtoQ : (KstalkFunctor p) ≅ (EvalInP p ) := asIso (StalkToPFunc p)

end

#lint
