import Mathlib
import Mathlib.Topology.Separation
import M2.alpha

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite

variable (X) [TopologicalSpace X] [T2Space X]


noncomputable section
variable (K:Compacts X) (U:Opens X)
variable (F:(Opens X)ᵒᵖ⥤ Ab)

--a^*P et a^*Q rel sont isomorphes si P et Q sont sympa
section

variable (P Q:Opens X → Prop) (hpq:∀ (U:Opens X), P U → Q U)

variable (K1 K2: Compacts X) (f:K1 ⟶  K2)

def K2subUPtoK1subUP: (KsubU_cat X K2 P) ⥤ (KsubU_cat X K1 P ) where
  obj U:= ⟨U.obj,⟨Set.Subset.trans (leOfHom f) U.property.1,U.property.2⟩⟩
  map f:= homOfLE (leOfHom f)


def KsubUPtoQ : (KsubU_cat X K P) ⥤  (KsubU_cat X K Q ):= FullSubcategory.map (fun U => fun hP=> ⟨hP.1, hpq U hP.2⟩)

variable (V: ∀ K, KsubU_cat X K Q → KsubU_cat X K P)

variable (V_spec: ∀ K,∀ U, (V K U).obj.carrier ⊆ U.obj.carrier)

variable (axiomP: ∀ U1 U2, P U1 → P U2 → P (U1 ⊔ U2))

variable (c:Cocone (FU X K F P))

lemma diagram_commute (U:KsubU_cat X K Q) (V1 V2: KsubU_cat X K P) (h1: op U.obj ⟶ op V1.obj) (h2: op U.obj ⟶ op V2.obj): F.map h1 ≫ c.ι.app { unop := V1 }= F.map h2 ≫ c.ι.app { unop := V2 }:= by

  let V1cupV2:= op (⟨V1.obj ⊔ V2.obj, ⟨Set.Subset.trans V1.property.1 (Set.subset_union_left) , axiomP _  _ V1.property.2 V2.property.2⟩⟩: (KsubU_cat X K P))

  let g:F.obj { unop := U.obj } ⟶ F.obj { unop := V1cupV2.unop.obj }:= by
    apply F.map (op (homOfLE _) )
    exact sup_le (leOfHom h1.unop) (leOfHom h2.unop)

  let f1:F.obj { unop := V1cupV2.unop.obj } ⟶ F.obj { unop := V1.obj }:= by
    apply F.map (op (homOfLE _) )
    apply le_sup_left

  let f2:F.obj { unop := V1cupV2.unop.obj } ⟶ F.obj { unop := V2.obj }:= by
    apply F.map (op (homOfLE _) )
    apply le_sup_right

  apply @Eq.trans _ _ (g≫ f1 ≫ c.ι.app (op V1))

  rw [← Category.assoc]
  apply eq_whisker
  rw [← F.map_comp]
  apply congrArg
  rfl

  apply @Eq.trans _ _ (g≫ f2 ≫ c.ι.app (op V2))

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

def CoconePtoQι :FU X K F Q ⟶ (Functor.const (KsubU_cat X K Q)ᵒᵖ).obj c.pt where
  app U := by
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
    rw [← Category.assoc,← F.map_comp]
    apply diagram_commute
    repeat assumption

def CoconePtoQ : Cocone (FU X K F Q) where
  pt:= c.pt
  ι:= CoconePtoQι X K F P Q V V_spec axiomP c

def PtoQhom :(colimit.cocone (FU X K F Q)) ⟶ (CoconePtoQ X K F P Q V V_spec axiomP (colimit.cocone (FU X K F P))) where
  hom:=colimit.desc (FU X K F Q) (CoconePtoQ X K F P Q V V_spec axiomP (colimit.cocone (FU X K F P)))
  w U:= by simp


variable (d:Cocone (FU X K F Q))


def CoconeQtoPι :FU X K F P ⟶ (Functor.const (KsubU_cat X K P)ᵒᵖ).obj d.pt where
  app U:= d.ι.app  (op ((KsubUPtoQ X K P Q hpq).obj U.unop))
  naturality _ _ f:=d.ι.naturality (op ((KsubUPtoQ X K P Q hpq).map f.unop))


def CoconeQtoP : Cocone (FU X K F P) where
  pt := d.pt
  ι:= CoconeQtoPι X K F P Q hpq d

def IsColPtoQ: IsColimit (CoconePtoQ X K F P Q V V_spec axiomP (colimit.cocone (FU X K F P))) where
  desc s := colimit.desc (FU X K F P) (CoconeQtoP X K F P Q hpq s)
  fac s _:= by
    unfold CoconePtoQ CoconePtoQι CoconeQtoP CoconeQtoPι KsubUPtoQ
    simp
    apply s.ι.naturality
  uniq s m h := by
    apply @colimit.hom_ext _ _ _ _ (FU X K F P)
    intro U

    unfold CoconeQtoP CoconeQtoPι KsubUPtoQ
    simp
    rw [← h]
    unfold CoconePtoQ CoconePtoQι
    simp
    rw [← Category.assoc]
    apply eq_whisker

    let h:= (colimit.cocone (FU X K F P)).ι.naturality

    apply Eq.trans _
    apply Eq.trans
    apply Eq.symm (h _)

    exact op (V K ((KsubUPtoQ X K P Q hpq).obj U.unop))
    apply op (homOfLE (V_spec _ _))
    repeat rfl

def isoPtoQ: IsIso (PtoQhom X K F P Q V V_spec axiomP):= IsColimit.hom_isIso (colimit.isColimit (FU X K F Q)) (IsColPtoQ X K F P Q hpq V V_spec axiomP ) _


def AlphaUpFPtoQ : (AlphaUpStarF X F Q)⟶ (AlphaUpStarF X F P) where
  app K:= (PtoQhom X K.unop F P Q V V_spec axiomP).hom

  naturality := by
    intro K1 K2 f
    apply colimit.hom_ext
    intro U
    unfold AlphaUpStarF K1subK2natTrans CoconePtoQ CoconePtoQι K1subK2subU PtoQhom CoconePtoQ CoconePtoQι
    simp

    apply diagram_commute _ _ _ _ _ axiomP _ ((K2subUPtoK1subUP X Q K2.unop K1.unop f.unop).obj U.unop)


def AlphaUpPQtoP : (AlphaUpStarP X Q)⟶ (AlphaUpStarP X P) where
  app F:= (AlphaUpFPtoQ X F P Q V V_spec axiomP)
  naturality F1 F2 τ:= by
    apply NatTrans.ext
    apply funext
    intro _
    apply colimit.hom_ext
    unfold AlphaUpStarP AlphaUpStarTau AlphaUpFPtoQ τres PtoQhom CoconePtoQ CoconePtoQι
    simp

theorem IsIsoAlphaUpPtoQ : IsIso (AlphaUpPQtoP X P Q V V_spec axiomP ):= by
  apply ( NatTrans.isIso_iff_isIso_app _).2
  intro F
  unfold AlphaUpPQtoP
  simp
  apply ( NatTrans.isIso_iff_isIso_app _).2
  intro K

  unfold AlphaUpFPtoQ
  simp

  rcases (isoPtoQ X K.unop F P Q hpq V V_spec axiomP).out with ⟨i,hi⟩
  use i.hom
  constructor
  rw [← Cocone.category_comp_hom, hi.1]
  unfold AlphaUpStarP AlphaUpStarF
  simp

  rw [← Cocone.category_comp_hom, hi.2]
  unfold AlphaUpStarP AlphaUpStarF CoconePtoQ
  simp

def IsoAlphaUpPtoQ: (AlphaUpStarP X Q) ≅ (AlphaUpStarP X P):= by
  let h:= IsIsoAlphaUpPtoQ X P Q hpq V V_spec axiomP
  apply asIso (AlphaUpPQtoP X P Q V V_spec axiomP )

end

section --α^* variante avec seulement les U relativements comapcts

variable [LocallyCompactSpace X]
--P
def relcCond: Opens X → Prop := (fun (U:Opens X) => IsCompact (closure U.carrier))
--Q
#check trueCond

def AlphaUpStarRc : ((Opens X)ᵒᵖ ⥤ Ab) ⥤ (Compacts X)ᵒᵖ ⥤ Ab := AlphaUpStarP _ (relcCond X)

lemma hpq:∀ (U:Opens X), (relcCond X) U  → (trueCond X) U:= λ _ _ => rfl

lemma existsIntermed (h: K.carrier ⊆ U.carrier):Nonempty ({ L //IsCompact L ∧ K.carrier ⊆ interior L ∧ L ⊆ U.carrier}):= by
  rcases (exists_compact_between K.isCompact U.isOpen h ) with ⟨L,hL⟩
  exact Nonempty.intro ⟨L,hL⟩

lemma IntSubSelf (U:Set X) : interior U⊆U:= by
  unfold interior
  intro _
  simp
  intro _ _ htu hat
  exact htu hat

def V K: KsubU_cat X K (trueCond X) → KsubU_cat X K (relcCond X):= by
  intro U
  let L:=(Classical.choice (existsIntermed X K U.obj U.property.1)).val
  use ⟨interior L,@isOpen_interior X L _⟩

  unfold KsubU
  constructor
  exact (Classical.choice (existsIntermed X K U.obj U.property.1)).property.2.1
  unfold relcCond
  apply IsCompact.of_isClosed_subset
  exact (Classical.choice (existsIntermed X K U.obj U.property.1)).property.1
  apply isClosed_closure

  intro a ha
  apply ha
  constructor
  apply IsCompact.isClosed
  exact (Classical.choice (existsIntermed X K U.obj U.property.1)).property.1

  apply IntSubSelf

lemma V_spec: ∀ K,∀ U, (V X K U).obj.carrier ⊆ U.obj.carrier:= by
  intro K U
  unfold V
  simp
  apply Set.Subset.trans
  apply IntSubSelf
  exact (Classical.choice (existsIntermed X K U.obj U.property.1)).property.2.2

lemma axiomP: ∀ U1 U2, (relcCond X) U1 → (relcCond X) U2 → (relcCond X) (U1 ⊔ U2):= by
  intro U1 U2 h1 h2
  unfold relcCond
  simp
  exact IsCompact.union h1 h2

def AlphaUpStarToRc : (AlphaUpStar X) ≅ (AlphaUpStarRc X):= by
  apply IsoAlphaUpPtoQ _ _ _ _ _ _ _
  exact λ _ _ => rfl
  exact V X
  exact (V_spec X)
  exact axiomP X

def AdjAlphaStarRc : (AlphaUpStarRc X ) ⊣ (AlphaDownStar X ) := Adjunction.ofNatIsoLeft (AdjAlphaStar X) (AlphaUpStarToRc X)
