import Mathlib
import Mathlib.Topology.Separation

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite

variable (X) [TopologicalSpace X] [T2Space X]
variable (U:Opens X) (K:Compacts X)
variable (F:(Compacts X)ᵒᵖ ⥤ Ab) (K1:Compacts X) (K2:Compacts X)

--La limite
def RelCN (K:Compacts X) : Set (Opens X) := fun (U:Opens X) => (K.carrier ⊆ U.carrier) ∧ IsCompact (closure U.carrier)

def RelCN_cat (K:Compacts X) : Type := FullSubcategory (RelCN X K)

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

def FUbar : (RelCN_cat X K)ᵒᵖ ⥤ Ab := Functor.comp (closureFunc X K).op  F

def FK_transNat: (FUbar X K F) ⟶ ((Functor.const (RelCN_cat X K)ᵒᵖ).obj (op K)).comp F where
app W:= by
  apply F.map
  apply op
  apply homOfLE
  apply Set.Subset.trans (W.unop).property.1
  unfold closureFunc closure
  intro a ha
  simp [Set.mem_iInter]
  intro t _ hwt
  exact hwt ha
naturality := by
  intros W Y f
  unfold FUbar closureFunc
  simp
  rw [← F.map_comp]
  rfl

def FK : Cocone (FUbar X K F):= Cocone.mk (F.obj (op K)) ((FK_transNat X K F)  ≫ ((Functor.constComp _ _ _).hom))

--Le complexe à 4 terme

open ZeroObject DirectSum

def ZtoFK1uK2:= (0: 0 ⟶ F.obj { unop := K1 ⊔ K2 })

#check F.map (op  (homOfLE (@inf_le_left _ _ K1 K2)))

#check F.map (op  (homOfLE (@inf_le_right _ _ K1 K2)))

#check F.map (op  (homOfLE (@le_sup_left _ _ K1 K2)))

#check F.map (op  (homOfLE (@le_sup_right _ _ K1 K2)))

variable (A B:Ab)


#check (A ⊕ B)

#check ComposableArrows.mk₃

--def complex : ComposableArrows Ab 3:= CategoryTheory.ComposableArrows.mk₃ (ZtoFK1uK2 X F K1 K2)  _ _ --sorry


structure Ksheaf where
  F : (Compacts X)ᵒᵖ ⥤ Ab
  ksh1 : F.obj (op (⊥:Compacts X)) = zero
  ksh2 : ∀ K1 K2 :Compacts X, sorry
  ksh3 : ∀ K:Compacts X, (IsIso (colimit.desc (FUbar X K F) (FK X K F)))
