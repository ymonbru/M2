import Mathlib

open Topology CategoryTheory TopologicalSpace

variable {X : Type } [TopologicalSpace X]

def TopologicalSpace.Opens.compactInsd (U : Opens X) : Set (Compacts X) := setOf (fun K ↦ K.carrier ⊆ U.carrier)

def baseChange {U V : Opens X} (h : U ⟶ V) : U.compactInsd → V.compactInsd := fun ⟨K,hK⟩ => ⟨K, fun _ hx => by apply Set.mem_of_subset_of_mem (leOfHom h) (hK hx)⟩

#min_imports
