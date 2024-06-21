import Mathlib
import Mathlib.Topology.Separation
import M2.alpha

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite

variable (X) [TopologicalSpace X] [T2Space X]

--α^* variante avec seulement les U relativements comapcts
noncomputable section
variable (K:Compacts X) (U:Opens X)
variable (F:(Opens X)ᵒᵖ⥤ Ab)

def relcCond: Opens X → Prop := (fun (U:Opens X) => IsCompact (closure U.carrier))

def AlphaUpStarRc : ((Opens X)ᵒᵖ ⥤ Ab) ⥤ (Compacts X)ᵒᵖ ⥤ Ab := AlphaUpStarP _ (relcCond X)
--a^* et a^* rel calculent la même chose
section

variable (P Q:Opens X → Prop) (hpq:∀ (U:Opens X), P U → Q U)

def KsubUPtoQ : (KsubU_cat X K P) ⥤  (KsubU_cat X K Q ):= FullSubcategory.map (fun U => fun hP=> ⟨hP.1, hpq U hP.2⟩)

lemma commuteFPtoFQ: (FU X K F P) = Functor.comp (KsubUPtoQ X K P Q hpq).op (FU X K F Q):= by
  rfl

--lemma relcToTrue:∀ U,(relcCond X) U → (trueCond X) U:= λ _ _ => rfl


variable (V: ∀ K, KsubU_cat X K Q → KsubU_cat X K P)

variable (V_spec: ∀ K,∀ U, (V K U).obj.carrier ⊆ U.obj.carrier)

variable (axiomP: ∀ U1 U2, P U1 → P U2 → P (U1 ⊔ U2))

variable (c:Cocone (FU X K F P))

def CoconePtoQι :FU X K F Q ⟶ (Functor.const (KsubU_cat X K Q)ᵒᵖ).obj c.pt where
  app := by
    intro U
    unfold FU
    simp
    apply CategoryStruct.comp
    apply F.map (_ :_⟶ op (V K U.unop).obj )
    apply op (homOfLE (V_spec _ _))
    exact c.ι.app (op (V K U.unop))
  naturality := by
    intro U1 U2 f
    unfold FU
    simp
    --je fais commuter un diagramme à peut près similaire plus tard, à voir si je ne peut pas extraire un lemme
    let V1cupV2:= op (⟨(V K U1.unop).obj ⊔ (V K U2.unop).obj, ⟨Set.Subset.trans (V K U1.unop).property.1 (Set.subset_union_left) , axiomP _  _ (V K U1.unop).property.2 (V K U2.unop).property.2⟩⟩: (KsubU_cat X K P))

    let g:F.obj { unop := U1.unop.obj } ⟶ F.obj { unop := V1cupV2.unop.obj }:= by
      apply F.map (op (homOfLE _) )
      exact (sup_le (V_spec _ _) (Set.Subset.trans (V_spec _ _) (leOfHom f.unop)))

    let h2:F.obj { unop := V1cupV2.unop.obj } ⟶ F.obj { unop := (V K U2.unop).obj }:= by
      apply F.map (op (homOfLE _) )
      apply le_sup_right

    let h3:F.obj { unop := V1cupV2.unop.obj } ⟶ F.obj { unop := (V K U1.unop).obj }:= by
      apply F.map (op (homOfLE _) )
      apply le_sup_left


    apply @Eq.trans _ _ (g≫ h2 ≫ c.ι.app (op (V K U2.unop)))

    rw [← Category.assoc,← Category.assoc]
    apply eq_whisker
    rw [← F.map_comp,← F.map_comp]
    apply congrArg
    rfl

    apply @Eq.trans _ _ (g≫ h3 ≫ c.ι.app (op (V K U1.unop)))

    apply whisker_eq
    let h:= c.ι.naturality
    unfold FU at h
    simp at h

    apply Eq.trans
    apply h
    rw [← h]
    rfl

    rw [← Category.assoc]
    apply eq_whisker
    rw [← F.map_comp]
    rfl

def CoconePtoQ :Cocone (FU X K F Q) where
  pt:= c.pt
  ι:= CoconePtoQι X K F P Q V V_spec axiomP c


def machin :CoconeMorphism (colimit.cone (FU X K F Q)) (CoconePtoQ X K F P Q V V_spec axiomP (colimit.cocone (FU X K F P))) where
  hom:=colimit.desc (FU X K F Q) (CoconePtoQ X K F P Q V V_spec axiomP (colimit.cocone (FU X K F P)))



def AlphaUpPtoQ : (AlphaUpStarF X F Q)⟶ (AlphaUpStarF X F P) where
  app K:= colimit.desc (FU X K.unop F Q) (CoconePtoQ X K.unop F P Q (V) V_spec axiomP (colimit.cocone (FU X K.unop F P)))

  naturality := by
    intro K1 K2 f
    apply colimit.hom_ext
    intro U
    unfold AlphaUpStarF K1subK2natTrans CoconePtoQ CoconePtoQι K1subK2subU
    simp
    --a peut près le même diagrame que plus haut

    sorry

theorem machin:IsIso (AlphaUpPtoQ X F P Q V V_spec axiomP):= by
  apply ( NatTrans.isIso_iff_isIso_app _).2
  intro K
  unfold AlphaUpPtoQ
  simp

  apply IsColimit.hom_isIso

  sorry

end

#check 1+1
