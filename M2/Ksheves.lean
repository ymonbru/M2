import Mathlib
import Mathlib.Topology.Separation

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite

variable (X) [TopologicalSpace X] [T2Space X]
variable (U:Opens X) (K:Compacts X)
variable (F:(Compacts X)ᵒᵖ ⥤ Ab) (K1:Compacts X) (K2:Compacts X)

#check Quiver.Hom.op
#check Compacts X

#check (⊥:Compacts X)

--La limite
def RelCN (K:Compacts X) : Set (Opens X) := fun (U:Opens X) => (K.carrier ⊆ U.carrier) ∧ IsCompact (closure U.carrier)

def RelCN_cat (K:Compacts X) : Type := FullSubcategory (RelCN X K)
#check RelCN X (⊥:Compacts X)

instance : Category (RelCN_cat X K) := FullSubcategory.category (RelCN X K)

--surement déjà dans mathlib mais exo
lemma closure_increasing (U:Set X) (V:Set X) (h: U ⊆ V): closure U ⊆ closure V:= by
  intros a ha W hW
  unfold closure at ha
  simp [Set.mem_iInter] at ha
  apply ha _ hW.1
  exact Set.Subset.trans h hW.2

def closureFunc (K:Compacts X): (RelCN_cat X K) ⥤ (Compacts X)  where
  obj U := ⟨closure U.obj.carrier, U.property.2⟩
  map f :=  homOfLE (closure_increasing _ _ _ (leOfHom f))
  --map_id :=sorry
  --map_comp:= sorry

def ksh3 : (RelCN_cat X K)ᵒᵖ ⥤ Ab := Functor.comp (closureFunc X K).op  F

#check (Functor.const (RelCN X K)).obj (F.obj (op K)) ⟶ ksh3

#check colimit (Functor.comp (closureFunc X K).op  F)

variable (W: RelCN_cat X K)

#check F.obj ((closureFunc X K).op.obj (op W))






def FK : Cocone (ksh3 X K F):= Cocone.mk (F.obj (op K)) ({app := fun W => (ksh3 X K F).map _  , naturality := sorry} )

#check limit.lift

--Le complexe à 4 terme

#check homOfLE (@bot_le _ _ _ K1)

#check (zero:Ab)

#check 0 → F.obj (op (K1 ⊔ K2))


#check F.map (op  (homOfLE (@inf_le_left _ _ K1 K2)))

#check F.map (op  (homOfLE (@inf_le_right _ _ K1 K2)))

#check F.map (op  (homOfLE (@le_sup_left _ _ K1 K2)))

#check F.map (op  (homOfLE (@le_sup_right _ _ K1 K2)))


def complex (F:(Compacts X)ᵒᵖ ⥤ Ab) (K1:Compacts X) (K2:Compacts X): ComposableArrows Ab 3:= CategoryTheory.ComposableArrows.mk₃ sorry sorry sorry









structure Ksheaf where
  F : (Compacts X)ᵒᵖ ⥤ Ab
  ksh1 : F.obj (op (⊥:Compacts X)) = zero
  ksh2 : ∀ K1 K2 :Compacts X, sorry
  ksh3 : ∀ K:Compacts X, sorry
