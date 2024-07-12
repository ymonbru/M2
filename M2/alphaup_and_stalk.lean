import Mathlib
import Mathlib.Topology.Separation
import M2.alpha
import M2.K_stalks

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite TopCat TopCat.Presheaf
open ZeroObject

variable (X) [TopologicalSpace X] [T2Space X]
variable (p:X) (F:Presheaf Ab (of X))

@[app_unexpander Opposite.op]
def unexpandOp : Lean.PrettyPrinter.Unexpander
  | `($_ $x:term) => `($(Lean.mkIdent `op) $x) -- Ce `Lean.mkIdent` est un hack honteux.
  | _ => throw ()

noncomputable section

#check Functor.comp (AlphaUpStar) (KstalkFunctor p)
#check @stalkFunctor Ab _ _ (of X) p

/-- Functor from the neighbourhoods of p to the opens that contains p-/
@[simp]
def NhdsToPsubU : (@OpenNhds (of X) p) ⥤ (KsubU_cat (pC p) trueCond) where
  obj U := ⟨U.obj, Set.singleton_subset_iff.2 U.property,rfl⟩
  map f := homOfLE  (leOfHom f)

@[simp]
def ForgetPsub:(KsubU_cat (pC p) trueCond)⥤ (Opens X) := (inducedFunctor fun (U:KsubU_cat (pC p) trueCond) ↦ U.obj )

@[simp]
lemma hey :OpenNhds.inclusion p = (NhdsToPsubU _ _) ⋙ (ForgetPsub _ _):= by
  apply CategoryTheory.Functor.ext
  · intro _ _ _
    rfl
  · intro _
    rfl


/--The natural maps from F(U) (fo U containing p) to the stalk of F at p-/
@[simps]
def FUtoStalkι : FU (pC p) F (trueCond ) ⟶ (Functor.const _ ).obj (F.stalk p) where
  app U := germ _ ⟨p, U.unop.property.1 (by rfl)⟩ ≫ F.stalkSpecializes (by rfl)

  naturality U V _ := by
    suffices F.map _ ≫ F.germ ⟨_, V.unop.property.1 (by rfl)⟩ = F.germ ⟨_, U.unop.property.1 (by rfl)⟩ by simpa
    apply Presheaf.germ_res

/-The cocone induced by FUtoStalkι-/
@[simps]
def FUtoStalk : Cocone (FU (pC p) F (trueCond)):= Cocone.mk _ (FUtoStalkι X p F)

variable (c:Cocone (FU (pC p) F trueCond))

@[simps]
def truc :(OpenNhds.inclusion p).op ⋙ F ⟶ (Functor.const _).obj c.pt where
  app U:= (F.map <| op <| 𝟙 _) ≫  (c.ι.app <| op <| (@NhdsToPsubU (of X) _ (p:of X)).obj U.unop)
  naturality U V f := by
    beta_reduce
    simp



    --#check hey _ p
    --#check @hey X _ (p :of X)
    --simp
    --calc F.map { unop := 𝟙 ((OpenNhds.inclusion p).op.obj V).unop } ≫ c.ι.app { unop := (NhdsToPsubU (↑(of X)) p).obj V.unop } =
  --(F.map { unop := 𝟙 ((OpenNhds.inclusion p).op.obj U).unop } ≫ c.ι.app { unop := (NhdsToPsubU (↑(of X)) p).obj U.unop }) ≫
    --((Functor.const (OpenNhds p)ᵒᵖ).obj c.pt).map f :=by sorry


    --C'est c.ι.naturality mais avec plein de trucs qui encombrent
    /-let h := c.ι.naturality
    unfold FU KsubU at h
    dsimp at h
    #check ((NhdsToPsubU X p).obj V.unop)
    #check h (op ((NhdsToPsubU X p).map f.unop))-/
    --sorry






    --sorry
@[simps]
def transformation : Cocone ((OpenNhds.inclusion p).op ⋙ F) := Cocone.mk _ (truc X p F c)

instance :IsColimit (FUtoStalk X p F) where
  desc s := colimit.desc _ (transformation X p F s)
  fac s U := by
    simp


    sorry
  uniq s m hm := by
    simp
    unfold FUtoStalk at m
    simp at m
    apply Presheaf.stalk_hom_ext
    intro U hU

    simp


    sorry

def AlphaComStalkEval : (AlphaUpStar) ⋙ (EvalInP p)⟶ @stalkFunctor _ _ _ (of X) p  where
  app F := colimit.desc _ (FUtoStalk _ _ _)
  naturality F1 F2 τ :=by
    suffices colimMap (τres ⟨{p},_⟩ _ _ _ _) ≫ colimit.desc _ (FUtoStalk _ _ _) = _ by simpa
    apply colimit.hom_ext
    intro j
    rw [← Category.assoc]
    unfold pC

    --suffices τ.app { unop := j.unop.obj } ≫ germ F2 ⟨p, _⟩ = germ F1 ⟨p, _⟩ ≫ (stalkFunctor Ab p).map τ by simpa
    --pourquoi cette erreur?
    simp

    rw [ Presheaf.stalkFunctor_map_germ]

def AlphaComStalk : (AlphaUpStar) ⋙ (KstalkFunctor p)⟶ @stalkFunctor Ab _ _ (of X) p := whiskerLeft _ (IsoAlphaUpPtoQ _).hom ≫ AlphaComStalkEval _ _

instance : IsIso (AlphaComStalk X p):= by

  sorry

def IsoAlphaComStalk: (AlphaUpStar) ⋙ (KstalkFunctor p) ≅ @stalkFunctor Ab _ _ (of X) p:= asIso (AlphaComStalk X p)

--#lint
