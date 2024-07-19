import M2.alpha
import M2.K_stalks
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.Sheaves.Stalks

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite TopCat TopCat.Presheaf
open ZeroObject

variable (X) [TopologicalSpace X] [T2Space X]
variable {C} [Category C] [HasPullbacks C] [HasColimits C] [HasZeroObject C]
variable (p: of X) (F:Presheaf C (of X))

/-@[app_unexpander Opposite.op]
def unexpandOp : Lean.PrettyPrinter.Unexpander
  | `($_ $x:term) => `($(Lean.mkIdent `op) $x) -- Ce `Lean.mkIdent` est un hack honteux.
  | _ => throw ()-/

noncomputable section

#check Functor.comp (AlphaUpStar) (KstalkFunctor p)
#check @stalkFunctor C _ _ (of X) p

/-- Functor from the neighbourhoods of p to the opens that contains p-/
@[simp]
def NhdsToPsubU : (@OpenNhds (of X) p) ⥤ (KsubU_cat (pC p) trueCond) where
  obj U := ⟨U.obj, Set.singleton_subset_iff.2 U.property,rfl⟩
  map f := homOfLE  (leOfHom f)

--@[simp]
--def ForgetPsub:(KsubU_cat (pC p) trueCond)⥤ (Opens X) := (inducedFunctor fun (U:KsubU_cat (pC p) trueCond) ↦ U.obj )

/-@[simp]
lemma hey :OpenNhds.inclusion p = (NhdsToPsubU _ _) ⋙ (ForgetPsub _ _):= by
  apply CategoryTheory.Functor.ext
  · intro _ _ _
    rfl
  · intro _
    rfl-/

/--The natural maps from F(U) (fo U containing p) to the stalk of F at p-/
@[simps]
def FUtoStalkι : FU (pC p) F (trueCond ) ⟶ (Functor.const _ ).obj (F.stalk p) where
  app U := germ _ ⟨p, U.unop.property.1 (by rfl)⟩ ≫ F.stalkSpecializes (by rfl)

  naturality U V _ := by
    suffices _ = F.germ ⟨_, U.unop.property.1 (by rfl)⟩ by simpa
    apply Presheaf.germ_res

/-The cocone induced by FUtoStalkι-/
@[simps]
def FUtoStalk : Cocone (FU (pC p) F (trueCond)):= Cocone.mk _ (FUtoStalkι X p F)

variable (c:Cocone (FU (pC p) F trueCond))

@[simps]
def CoconeFUpCtoOPenNhdspι :(OpenNhds.inclusion p).op ⋙ F ⟶ (Functor.const _).obj c.pt where
  app U:= c.ι.app <| op <| (@NhdsToPsubU (of X) _ (p:of X)).obj U.unop
  naturality U V f := by
    have : ∀ (X Y : (KsubU_cat (pC p) trueCond)ᵒᵖ) (f : X ⟶ Y), F.map f.unop.op ≫ c.ι.app Y = c.ι.app X ≫ 𝟙 c.pt := by
      apply c.ι.naturality
    suffices _ = c.ι.app (op ⟨U.unop.obj, _ ⟩ ) ≫ 𝟙 c.pt by simpa
    rw [← this]
    apply congr
    repeat rfl

@[simps]
def CoconeFUpCtoOPenNhdsp : Cocone ((OpenNhds.inclusion p).op ⋙ F) := Cocone.mk _ (CoconeFUpCtoOPenNhdspι X p F c)

instance :IsColimit (FUtoStalk X p F) where
  desc s := colimit.desc _ (CoconeFUpCtoOPenNhdsp X _ F s)
  fac s U := by
    suffices s.ι.app (op ⟨U.unop.obj,_⟩ ) = s.ι.app U by simpa [germ]
    rfl
  uniq s m hm := by
    apply Presheaf.stalk_hom_ext
    intro U hU
    suffices colimit.ι ((OpenNhds.inclusion p).op ⋙ F) (op ⟨U , _⟩) ≫ m = s.ι.app (op ⟨U , _⟩) by simpa [germ]
    rw [← hm ]
    simp [germ]

variable (C)

def AlphaComStalkEval : (AlphaUpStar) ⋙ (EvalInP C p)⟶ @stalkFunctor _ _ _ (of X) p  where
  app F := colimit.desc _ (FUtoStalk _ _ _)
  naturality _ _ _ := by
    suffices _ = colimit.desc (FU _ _ _) (FUtoStalk _ _ _) ≫ _ by simpa
    apply colimit.hom_ext
    intro _
    rw [← Category.assoc]
    suffices  _ = germ _ _ ≫ _ by simpa
    rw [ Presheaf.stalkFunctor_map_germ]


def AlphaComStalk : (AlphaUpStar) ⋙ (KstalkFunctor p)⟶ @stalkFunctor C _ _ (of X) p := whiskerLeft _ (IsoAlphaUpPtoQ C p).hom ≫ AlphaComStalkEval _ _ _

instance : IsIso (AlphaComStalk X C p):= by
  suffices IsIso (AlphaComStalkEval X C p) by apply IsIso.comp_isIso
  apply ( NatTrans.isIso_iff_isIso_app _).2
  intro F
  --simp
  unfold AlphaComStalkEval
  simp
  --apply IsColimit.hom_isIso
  --IsColimit.hom_isIso (colimit.isColimit (FU _ _ _)) (IsColPtoQ _ _ hpq _ _ _ ) _


  sorry

def IsoAlphaComStalk: (AlphaUpStar) ⋙ (KstalkFunctor p) ≅ @stalkFunctor C _ _ (of X) p:= asIso (AlphaComStalk X C p)

--#lint
