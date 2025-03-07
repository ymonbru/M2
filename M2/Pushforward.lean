import M2.Ksheaves
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Topology.Sets.Compacts
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Sheaves.Functors
--import M2.RCalpha

open CategoryTheory Limits TopologicalSpace Compacts Opposite Functor TopCat

variable {C} [Category C] [HasPullbacks C] [HasColimits C] [HasZeroObject C]
variable {X Y} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]

variable (f : X → Y) (proper_f : IsProperMap f)

@[simps!]
def preimageCompact : Compacts Y ⥤ Compacts X where
  obj K := ⟨f ⁻¹' K.carrier , IsProperMap.isCompact_preimage  proper_f K.isCompact'⟩
  map i := homOfLE (fun  _ ha => leOfHom i ha)

@[simps!]
def preimageOpen : Opens Y ⥤ Opens X := (Opens.map (ofHom ( ContinuousMap.mk f proper_f.toContinuous)) )

@[simps!]
def fDownStar : ((Compacts X)ᵒᵖ ⥤ C) ⥤ ((Compacts Y)ᵒᵖ ⥤ C) := (whiskeringLeft _ _ _ ).obj (preimageCompact f proper_f).op

#check (Opens.map (ofHom ⟨f, proper_f.toContinuous⟩ ) : Opens  Y ⥤ Opens X)

--lemma truc : (closureFunc Y ) ≫ (preimageCompact f proper_f) ⟶ Opens.map (ofHom ⟨f, proper_f.toContinuous⟩ ) ≫ (closureFunc X):= by sorry

open ZeroObject
variable (C) ( F : (Compacts X)ᵒᵖ ⥤ C) [LocallyCompactSpace X]-- the locally compact is here for the non emptyness of RelCN_cat

instance : Nonempty (RelCN_cat X K) := by
  have : IsOpen (⊤ : Set X)  := isOpen_univ
  have this2 : K.carrier ⊆ ⊤ := by
    intro _ _
    trivial
  rcases (exists_compact_between K.isCompact this this2 ) with ⟨L,hL⟩
  use ⟨interior L,@isOpen_interior X L _⟩
  constructor
  · exact hL.2.1
  · apply IsCompact.of_isClosed_subset hL.1 (isClosed_closure )
    intro a ha
    apply ha
    constructor
    · exact IsCompact.isClosed hL.1
    · apply interior_subset



instance  : IsCofiltered (RelCN_cat X K)  where
  cone_objs U1 U2:= by

    sorry
  cone_maps := by sorry




lemma fDS_ksh1 (hyp : F.obj (op (⊥ : Compacts _)) = 0) : ((fDownStar f proper_f).obj F).obj (op (⊥ : Compacts _)) = 0 := hyp

def fDS_ksh2 (hyp : ∀ K₁ K₂ : Compacts X, IsLimit (SquareSuptoInf F K₁ K₂ )) ( K₁ K₂ :Compacts Y): IsLimit (SquareSuptoInf ((fDownStar f proper_f).obj F) K₁ K₂ ) := hyp ((preimageCompact f proper_f).obj K₁) ((preimageCompact f proper_f).obj K₂)

#check IsColimit.hom_isIso
variable (K:Compacts Y)

def preimageRes : RelCN_cat Y K ⥤ RelCN_cat X ((preimageCompact f proper_f).obj K) where
  obj U := by
    use (preimageOpen f proper_f).obj U.obj

    constructor
    exact Set.preimage_mono U.property.1
    exact IsCompact.of_isClosed_subset (IsProperMap.isCompact_preimage proper_f U.property.2) isClosed_closure (Continuous.closure_preimage_subset (proper_f.toContinuous) U.obj.carrier)
  map _ := (preimageOpen f proper_f).map _


#check colimit.pre (FUbar X _ F ) (Functor.op (preimageRes f proper_f K))

def fDS_ksh3 (hyp : ∀ K : Compacts X, (IsColimit (FK _ K F))) :  ∀ K : Compacts Y, (IsColimit (FK _ K ((fDownStar f proper_f).obj F))) := by

  intro K
  let Ka := (preimageCompact f proper_f).obj K
  let machin := colimit.pre (FUbar X Ka F ) (Functor.op (preimageRes f proper_f K))

  have : IsCofilteredOrEmpty (RelCN_cat Y K) := by
    apply IsCofilteredKsubU
    apply axiomPrc
  have : (preimageRes f proper_f K).Initial := by
    apply (Functor.initial_iff_of_isCofiltered _).2
    constructor
    · intro U
    --lemme de topologie de Pardon
      sorry
    · intro _ U _ _
      use U
      use 𝟙 _
      rfl


  have : (preimageRes f proper_f K).op.Final := by
    apply final_op_of_initial

  have : _ := (Functor.Final.isColimitWhiskerEquiv ((preimageRes f proper_f K).op)  ((FK X Ka F))).invFun (hyp Ka)
  -- les deux ne sont pas égaux mais on doit pouvoir trouver un lien...

  sorry
