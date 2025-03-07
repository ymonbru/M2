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

variable {f : X → Y} (proper_f : IsProperMap f)

@[simps!]
def preimageCompact : Compacts Y ⥤ Compacts X where
  obj K := ⟨f ⁻¹' K.carrier , IsProperMap.isCompact_preimage  proper_f K.isCompact'⟩
  map i := homOfLE (fun  _ ha => leOfHom i ha)

@[simps!]
def preimageOpen : Opens Y ⥤ Opens X := (Opens.map (ofHom ( ContinuousMap.mk f proper_f.toContinuous)) )

@[simps!]
def fDownStar : ((Compacts X)ᵒᵖ ⥤ C) ⥤ ((Compacts Y)ᵒᵖ ⥤ C) := (whiskeringLeft _ _ _ ).obj (preimageCompact proper_f).op

#check (Opens.map (ofHom ⟨f, proper_f.toContinuous⟩ ) : Opens  Y ⥤ Opens X)

open ZeroObject
variable (C) ( F : (Compacts X)ᵒᵖ ⥤ C) (K : Compacts X) [LocallyCompactSpace X]-- the locally compact is here for the non emptyness of RelCN_cat

instance : Nonempty (RelCN_cat K) := by
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



omit [HasPullbacks C] [HasColimits C] [LocallyCompactSpace X] in
lemma fDS_ksh1 (hyp : F.obj (op (⊥ : Compacts _)) = 0) : ((fDownStar proper_f).obj F).obj (op (⊥ : Compacts _)) = 0 := hyp

def fDS_ksh2 (hyp : ∀ K₁ K₂ : Compacts X, IsLimit (SquareSuptoInf F K₁ K₂ )) ( K₁ K₂ :Compacts Y): IsLimit (SquareSuptoInf ((fDownStar proper_f).obj F) K₁ K₂ ) := hyp ((preimageCompact proper_f).obj K₁) ((preimageCompact proper_f).obj K₂)

#check IsColimit.hom_isIso
variable (K:Compacts Y)

def preimageRes : RelCN_cat K ⥤ RelCN_cat ((preimageCompact proper_f).obj K) where
  obj U := by
    use (preimageOpen proper_f).obj U.obj

    constructor
    exact Set.preimage_mono U.property.1
    exact IsCompact.of_isClosed_subset (IsProperMap.isCompact_preimage proper_f U.property.2) isClosed_closure (Continuous.closure_preimage_subset (proper_f.toContinuous) U.obj.carrier)
  map _ := (preimageOpen proper_f).map _

instance : (preimageRes proper_f K).Initial := by
    apply (Functor.initial_iff_of_isCofiltered _).2
    constructor
    · intro U
    --lemme de topologie de Pardon
      sorry
    · intro _ U _ _
      use U
      use 𝟙 _
      rfl

def preimageResSubSub : supSupK_cat K ⥤ supSupK_cat ((preimageCompact proper_f).obj K) where
  obj L := by
    use (preimageCompact proper_f).obj L.obj
    rcases L.property with ⟨U, hU1, hU2⟩
    use (preimageOpen proper_f).obj U
    constructor
    · intro _ ha
      exact hU1 ha
    · intro _ ha
      exact hU2 ha
  map _ := (preimageCompact proper_f).map _

instance : (preimageResSubSub proper_f K).Initial := by
    apply (Functor.initial_iff_of_isCofiltered _).2
    constructor
    · intro U
    --lemme de topologie de Pardon
      sorry
    · intro _ U _ _
      use U
      use 𝟙 _
      rfl

#check colimit.pre (FUbar _ F ) (Functor.op (preimageRes proper_f K))

def fDS_ksh3' (hyp : ∀ K : Compacts X, (IsColimit (FUbarToFK K F))) :  ∀ K : Compacts Y, (IsColimit (FUbarToFK K ((fDownStar proper_f).obj F))) := by

  intro K
  let Ka := (preimageCompact proper_f).obj K

  have : _ := (Functor.Final.isColimitWhiskerEquiv ((preimageRes proper_f K).op)  ((FUbarToFK Ka F))).invFun (hyp Ka)
  -- les deux ne sont pas égaux mais on doit pouvoir trouver un lien...

  sorry

def fDS_ksh3 (hyp : ∀ K : Compacts X, (IsColimit (FLToFK K F))) :  ∀ K : Compacts Y, (IsColimit (FLToFK K ((fDownStar proper_f).obj F))) := by

  intro K
  let Ka := (preimageCompact proper_f).obj K
  #check (hyp Ka)


  let machin := (Functor.Final.isColimitWhiskerEquiv ((preimageRes proper_f K).op) ((FLToFK Ka F))).invFun (hyp Ka)


  -- les deux ne sont pas égaux mais on doit pouvoir trouver un lien...

  sorry
