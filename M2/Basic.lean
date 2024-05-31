import Mathlib
import Mathlib.Topology.Separation

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite

variable (X) [TopologicalSpace X] [T2Space X]
variable (U:Opens X)

#check Compacts X



#check (⊥:Compacts X)



def RelCN (K:Compacts X) : Set (Opens X):= fun (U:Opens X) => (K.carrier ⊆ U.carrier) ∧ IsCompact (closure U.carrier)

#check RelCN X (⊥:Compacts X)


variable (F:(Compacts X)ᵒᵖ ⥤ Ab) (K1:Compacts X) (K2:Compacts X)



#check LE.le.hom (@bot_le _ _ _ K1)

#check (zero:Ab)

#check 0 → F.obj (op (K1 ⊔ K2))


#check F.map (op  (LE.le.hom (@inf_le_left _ _ K1 K2)))

#check F.map (op  (LE.le.hom (@inf_le_right _ _ K1 K2)))

#check F.map (op  (LE.le.hom (@le_sup_left _ _ K1 K2)))

#check F.map (op  (LE.le.hom (@le_sup_right _ _ K1 K2)))


def complex (F:(Compacts X)ᵒᵖ ⥤ Ab) (K1:Compacts X) (K2:Compacts X): ComposableArrows Ab 3:= CategoryTheory.ComposableArrows.mk₃ sorry sorry sorry









structure Ksheaf where
  F : (Compacts X)ᵒᵖ ⥤ Ab
  ksh1 : F.obj (op (⊥:Compacts X)) = zero
  ksh2 : ∀ K1 K2 :Compacts X, sorry
  ksh3 : ∀ K:Compacts X, sorry


def hello:= "world"
