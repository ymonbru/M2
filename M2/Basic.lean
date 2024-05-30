import Mathlib

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite

variable (X) [TopologicalSpace X]
variable (U:Opens X)


#check Compacts X

#check (⊥:Compacts X)

def RelCN (K:Compacts X) : Set (Opens X):= fun (U:Opens X) => (K.carrier ⊆ U.carrier) ∧ IsCompact (closure U.carrier)

#check RelCN X (⊥:Compacts X)


structure Ksheaf where
  F : (Compacts X)ᵒᵖ ⥤ Ab
  ksh1 : F.obj (op (⊥:Compacts X)) = zero
  ksh2 : ∀ K1 K2 :Compacts X, sorry
  ksh3 : ∀ K:Compacts X, sorry


def hello:= "world"
