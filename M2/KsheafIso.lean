import M2.Ksheaves

open CategoryTheory Limits TopologicalSpace Compacts Opposite

universe u v w

variable {X :Type w} [TopologicalSpace.{w} X] [T2Space.{w} X]
variable (K : Compacts X)

variable {C : Type u} [Category.{v, u} C]
variable (F : (Compacts X)ᵒᵖ ⥤ C) (G : Ksheaf X C) (τ : F ≅ G.carrier)
variable (K1 K2 : Compacts X)

noncomputable section

@[simps]
def DiagIsoKsh2 : cospan (FtoFInfLeft F K1 K2) (FtoFInfRight F K1 K2) ≅ cospan (FtoFInfLeft G.carrier K1 K2) (FtoFInfRight G.carrier K1 K2) where
  hom := natTransWcspFunc _ _ (τ.hom.app (op K1)) (τ.hom.app (op K2)) (τ.hom.app (op (K1 ⊓ K2))) (by simp [FtoFInfLeft]) (by simp [FtoFInfRight])
  inv := natTransWcspFunc _ _ (τ.inv.app (op K1)) (τ.inv.app (op K2)) (τ.inv.app (op (K1 ⊓ K2))) (by simp [FtoFInfLeft]) (by simp [FtoFInfRight])

@[simps!]
def CoconeIsoKsh2 : (SquareSuptoInf F K1 K2) ≅ (Cones.postcomposeEquivalence (DiagIsoKsh2 F G τ K1 K2)).inverse.obj (SquareSuptoInf G.carrier K1 K2) where
  hom := ⟨τ.hom.app _, by
    intro x
    match x with
      |.left => simp [FSuptoFLeft]
      |.right => simp [FSuptoFRight]
      |.one => simp[FtoFInfLeft, FSuptoFLeft]⟩
  inv := ⟨τ.inv.app _, by
    intro x
    match x with
      |.left => simp [FSuptoFLeft]
      |.right => simp [FSuptoFRight]
      |.one => simp[FtoFInfLeft, FSuptoFLeft]⟩

@[simps!]
def DiagIsoKsh3 : (FresSSK K F) ≅ (FresSSK K G.carrier) := (ObjectProperty.ι (supSupK K)).op.isoWhiskerLeft τ

def CoconeIsoKsh3: (FLToFK K F) ≅ (Cocones.precomposeEquivalence (DiagIsoKsh3 K F G τ)).functor.obj (FLToFK K G.carrier) where
  hom := ⟨τ.hom.app _, by aesop ⟩
  inv := ⟨τ.inv.app _, by aesop ⟩


def KsheafOfIso : Ksheaf X C where
  carrier := F
  ksh1 := by
    apply IsTerminal.ofIso G.ksh1
    exact τ.symm.app (op ⊥)
  ksh2 K1 K2 := by
    apply Limits.IsLimit.ofIsoLimit _ (CoconeIsoKsh2 F G τ K1 K2).symm
    apply IsLimit.ofPreservesConeTerminal
    exact G.ksh2 K1 K2
  ksh3 K := by
    apply Limits.IsColimit.ofIsoColimit _ (CoconeIsoKsh3 K F G τ).symm
    apply IsColimit.ofPreservesCoconeInitial
    exact G.ksh3 K
