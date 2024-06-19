import Mathlib
import Mathlib.Topology.Separation

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite

variable (X) [TopologicalSpace X] [T2Space X]
variable (K:Compacts X)
variable (F:(Compacts X)ᵒᵖ ⥤ Ab) (K1:Compacts X) (K2:Compacts X)

--La limite
def RelCN : Set (Opens X) := fun (U:Opens X) => (K.carrier ⊆ U.carrier) ∧ IsCompact (closure U.carrier)

def RelCN_cat : Type := FullSubcategory (RelCN X K)

instance : Category (RelCN_cat X K) := FullSubcategory.category (RelCN X K)

--surement déjà dans mathlib mais exo
lemma closure_increasing (U:Set X) (V:Set X) (h: U ⊆ V): closure U ⊆ closure V:= by
  intros a ha W hW
  unfold closure at ha
  simp [Set.mem_iInter] at ha
  apply ha _ hW.1
  exact Set.Subset.trans h hW.2

def closureFunc : (RelCN_cat X K) ⥤ (Compacts X)  where
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
  simp
naturality := by
  intros W Y f
  unfold FUbar
  simp
  rw [← F.map_comp]
  rfl

def FK : Cocone (FUbar X K F):= Cocone.mk (F.obj (op K)) ((FK_transNat X K F)  ≫ ((Functor.constComp _ _ _).hom))

--Le complexe à 4 terme

open ZeroObject
noncomputable section
def ZtoFcup:= (0: 0 ⟶ F.obj { unop := K1 ⊔ K2 })-- 0->F(K1∪ K2)

def FcuptoplusF:= F.map (op  (homOfLE (@le_sup_left _ _ K1 K2))) ≫ biprod.inl + F.map (op  (homOfLE (@le_sup_right _ _ K1 K2))) ≫ biprod.inr-- F(K1∪ K2)-> F(K1)⊞ F(K2)

def plusFtoFcap := biprod.fst ≫ F.map (op  (homOfLE (@inf_le_left _ _ K1 K2))) - biprod.snd ≫ F.map (op  (homOfLE (@inf_le_right _ _ K1 K2)))-- F(K1)⊞ F(K2)-> F(K1∩ K2)

def complex : ComposableArrows Ab 3:= CategoryTheory.ComposableArrows.mk₃ (ZtoFcup X F K1 K2)  (FcuptoplusF X F K1 K2) (plusFtoFcap X F K1 K2)


instance : ComposableArrows.IsComplex (complex X F K1 K2) where
  zero := by
    intros i hi
    unfold complex ZtoFcup FcuptoplusF plusFtoFcap
    --simp
    cases hi
    --F(K1∪ K2)-> F(K1)⊞ F(K2)-> F(K1)⊞ F(K2)-> F(K1∩ K2)=0
    dsimp
    repeat-- pourquoi ça ne marche pas si je ne le fais pas 2 fois?
      unfold ComposableArrows.Precomp.map
      dsimp
    simp
    repeat rw [← F.map_comp]
    apply sub_eq_zero_of_eq
    rfl
    induction i
    --0->F(K1∪ K2)->F(K1∪ K2)-> F(K1)⊞ F(K2)=0
    simp
    contradiction

--@[ext]
structure Ksheaf where
  carrier : (Compacts X)ᵒᵖ ⥤ Ab
  ksh1 : carrier.obj (op (⊥:Compacts X)) = 0 := by aesop_cat
  ksh2 : ∀ K1 K2 :Compacts X, (complex X carrier K1 K2).Exact := by aesop_cat
  ksh3 : ∀ K:Compacts X, (IsIso (colimit.desc (FUbar X K carrier) (FK X K carrier))) := by aesop_cat

instance:  Category (Ksheaf X) := InducedCategory.category (fun (F:Ksheaf X) => F.carrier)

#check Ksheaf X
