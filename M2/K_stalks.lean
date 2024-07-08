import Mathlib
import Mathlib.Topology.Separation
--import M2.Ksheaves

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite

variable {X} [TopologicalSpace X] [T2Space X]
variable (p : X)

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
def KstalkFunctor : ((Compacts X)ᵒᵖ ⥤ Ab)⥤ Ab where
  obj F := colimit (Fres p F)
  map _ := colimMap <| NatTrans.hcomp (NatTrans.id _) (by assumption)
  map_id := by
    intro F
    apply colimit.hom_ext
    intro K
    suffices 𝟙 _ ≫ colimit.ι (Fres p F) K = colimit.ι (Fres p F) K  by simp
    simp
  map_comp _ _ := by
    apply colimit.hom_ext
    intro _
    simp

/--The compact subset of X, induced by the singleton p (because X is Hausdorff)-/
@[simps]
def pC : Compacts X:=⟨{p},isCompact_singleton⟩

/-- The natural transformation that allows to define F(p) as a cocone of the diagram FUbar-/
@[simps]
def Fp_transNat : (Fres p F) ⟶ ((Functor.const (pinK_cat p)ᵒᵖ).obj <| op <| pC p).comp F where
app W:= F.map <| op <| homOfLE <| by
  intro _ hx
  rw [ Set.eq_of_mem_singleton hx]
  apply (W.unop).property

naturality  _ _ _:= by
  suffices F.map _ ≫ F.map _ = F.map _ by simpa
  rw [← F.map_comp]
  rfl

/-- The cocone of the diagram Fres, with point F(p) and the canonical maps-/
@[simps]
def Fp : Cocone (Fres p F) := Cocone.mk _ (Fp_transNat _ _  ≫ (Functor.constComp _ _ _).hom)

/--The functor that evaluate K-présheaves in {p}-/
@[simps]
def EvalInP : ((Compacts X)ᵒᵖ ⥤ Ab)⥤ Ab where
  obj F := (Fp p F ).pt
  map τ := τ.app <| op ⟨{p},isCompact_singleton⟩

/-- The compact subset {p} as a compact subset that contains p-/
@[simps]
def pC2: (pinK_cat p):=⟨pC p,rfl⟩

instance FpisCol : IsColimit (Fp p F) where
  desc s :=  s.ι.app <| op (pC2 p)
  fac s _ :=  s.ι.naturality _
  uniq s m hm := by
    dsimp --à faire disparaitre c'est la béta réduction
    rw [← hm (op (pC2 p))]
    suffices (Fp p F).ι.app (op (pC2 p)) = 𝟙 _ by
      rw [this]
      simp
    apply F.map_id


--@[simps]
/--The cone morphism from the stalk at p tp the cone with point F(p)-/
def StalkToP :(colimit.cocone (Fres p F))⟶ (Fp p F) where
  hom:= colimit.desc _ _
  w U:= by simp

instance IsIsoStalkToP: IsIso (StalkToP p F):= IsColimit.hom_isIso (colimit.isColimit _) (FpisCol _ _) _


/-- The canonical natural transformation from the stalk functor to the functor evaluation in p-/
@[simps]
def StalkToPFunc: (KstalkFunctor p)⟶ (EvalInP p )  where
  app _:=  (StalkToP p _).hom
  naturality _ _ _:= by
    apply colimit.hom_ext
    intro _
    unfold StalkToP EvalInP Fp Fp_transNat pC
    simp


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
def IsoAlphaUpPtoQ: (KstalkFunctor p) ≅ (EvalInP p ):= asIso (StalkToPFunc p)

end

--#lint
