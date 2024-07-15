import Mathlib
import Mathlib.Topology.Separation
import M2.alpha

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite

variable {X} [TopologicalSpace X] --[T2Space X]


noncomputable section
variable (K : Compacts X) (U : Opens X)
variable (F : (Opens X)ᵒᵖ⥤ Ab)

--a^* P et a^*Q are naturaly isomorphic if P et Q are nice enough
section

variable {P Q : Opens X → Prop} (hpq : ∀ (U : Opens X), P U → Q U)
variable {K1 K2 : Compacts X} (f : K1 ⟶ K2)

/-- The functor induced by P -> Q from the category of opens that contains K and satiffy P to the one that satisfy Q-/
@[simps!]
def KsubUPtoQ : (KsubU_cat K P) ⥤  (KsubU_cat K Q ):= FullSubcategory.map (fun _ => fun hP=> ⟨hP.1, hpq _ hP.2⟩)

variable (V : ∀ K, KsubU_cat K Q → KsubU_cat K P)

variable (V_spec : ∀ K,∀ U, (V K U).obj.carrier ⊆ U.obj.carrier)

variable (axiomP : ∀ U1 U2, P U1 → P U2 → P (U1 ⊔ U2))

variable (c : Cocone (FU K F P))

--@[simp]
lemma diagram_commute (U : KsubU_cat K Q) V1 V2 (h1 : op U.obj ⟶ op V1.obj) (h2 : op U.obj ⟶ op V2.obj) : F.map h1 ≫ c.ι.app (op V1) = F.map h2 ≫ c.ι.app (op V2):= by

  let V1cupV2op := op (⟨V1.obj ⊔ V2.obj, ⟨Set.Subset.trans V1.property.1 (Set.subset_union_left) , axiomP _  _ V1.property.2 V2.property.2⟩⟩: (KsubU_cat K P))

  let g : F.obj (op U.obj) ⟶ F.obj (op V1cupV2op.unop.obj):= by
    apply F.map <| op (homOfLE _ )
    exact sup_le (leOfHom h1.unop) (leOfHom h2.unop)

  let f1 : V1cupV2op ⟶ op  V1 := by
    apply op (homOfLE _ )
    apply le_sup_left

  let f2 :  V1cupV2op  ⟶ op V2 := by
    apply (op (homOfLE _ ) )
    apply le_sup_right

  calc F.map h1 ≫ c.ι.app { unop := V1 } = g≫ (FU _ _ _).map f1 ≫ c.ι.app (op V1) := by
    {
      rw [← Category.assoc]
      apply eq_whisker
      apply F.map_comp
    }
    _ = g ≫ (FU _ _ _).map f2 ≫ c.ι.app (op V2) := by
    {
      apply whisker_eq
      repeat rw [c.ι.naturality]
      rfl
    }
    _ = F.map h2 ≫ c.ι.app { unop := V2 } := by
    {
      rw [← Category.assoc]
      apply eq_whisker
      apply Eq.symm
      apply F.map_comp
    }

/-- The family of maps from F(U) such that Q(U) to a cone of the diagram of F(U) such that P(U) build by factorising along the path given by V-/
@[simps]
def CoconePtoQι : FU K F Q ⟶ (Functor.const _).obj c.pt where
  app U := by--enlever le mode tactique, mais il y a des trucs qu'il ne devine pas
    apply CategoryStruct.comp
    apply F.map (_ : _⟶ op (V _ U.unop).obj )
    apply op (homOfLE (V_spec _ _))
    exact c.ι.app (op (V _ U.unop))
  naturality U1 U2 _ := by
    suffices  F.map _ ≫ F.map _ ≫ c.ι.app (op (V _ U2.unop)) = F.map _ ≫ c.ι.app (op ( V _ U1.unop )) by simpa
    rw [← Category.assoc,← F.map_comp]
    apply diagram_commute
    repeat assumption

/-- The cone of the diagram of F(U) such that Q(U) induced by onne over the diagram of F(U) such that P(U) -/
@[simps]
def CoconePtoQ : Cocone (FU K F Q) := Cocone.mk _ (CoconePtoQι _ _ _ V_spec axiomP c)

/-- The morphisme of cocone from the colimit to CoconePtoQ-/
@[simps]
def QtoPhom : colimit.cocone (FU K F Q) ⟶ CoconePtoQ _ _ _ V_spec axiomP (colimit.cocone (FU _ _ _ )) where
  hom:=colimit.desc _ _
  --w _:= by simp


variable (d : Cocone (FU K F Q))

/-- The family of maps from F(U) such that P(U) to a cone of the diagram of F(U) such that Q(U) build by using the implication P -> Q -/
@[simps]
def CoconeQtoPι : FU K F P ⟶ (Functor.const _ ).obj d.pt where
  app _ := d.ι.app  (op ((KsubUPtoQ _ hpq).obj _))
  naturality _ _ _ := d.ι.naturality (op ((KsubUPtoQ _ hpq).map _))

/-- The cocone induced by CoconeQtoPι-/
@[simps]
def CoconeQtoP : Cocone (FU K F P) := Cocone.mk _ (CoconeQtoPι _ _ hpq d)

instance IsColPtoQ : IsColimit (CoconePtoQ K F _ V_spec axiomP (colimit.cocone (FU _ _ _))) where
  desc _ := colimit.desc _ (CoconeQtoP _ _ hpq _)
  fac s U := by
    suffices F.map _ ≫ s.ι.app (op ((KsubUPtoQ _ hpq).obj _ )) = s.ι.app U by simpa
    apply s.ι.naturality
  uniq s m h := by
    apply @colimit.hom_ext _ _ _ _ (FU _ _ _)
    intro U
    suffices colimit.ι (FU _ _ _) U ≫ _ = s.ι.app (op ((KsubUPtoQ _ hpq).obj U.unop))  by simpa
    rw [← h]
    suffices colimit.ι (FU _ _ _) _ ≫ _ = _ ≫ colimit.ι (FU _ _ _) _ ≫ _ by simpa
    rw [← Category.assoc]
    apply eq_whisker

    have f : U ⟶ _ := op (homOfLE (V_spec _ ((KsubUPtoQ _ hpq).obj U.unop)))

    calc colimit.ι (FU _ _ _) _ = (FU _ _ _).map f ≫ colimit.ι (FU _ _ _) _ := Eq.symm (colimit.w (FU K F P) f)
    _ = _ ≫ colimit.ι (FU _ _ _) _ := by rfl


instance isoQtoP: IsIso (QtoPhom K F _ V_spec axiomP):= IsColimit.hom_isIso (colimit.isColimit (FU _ _ _)) (IsColPtoQ _ _ hpq _ _ _ ) _

/-- The natural morphism from α^*_QF ⟶ α^ *_PF  -/
@[simps!]
def AlphaUpFQtoP : (AlphaUpStarF F Q)⟶ (AlphaUpStarF F P) where
  app _ := (QtoPhom _ _ _ V_spec axiomP).hom
  naturality _ _ f := by
    apply colimit.hom_ext
    intro _
    suffices _ ≫ colimit.ι (FU _ _ _ ) _ = _ ≫ colimit.ι _ _ by simpa
    apply diagram_commute _ _  axiomP _ ((K1subK2subU _ _ _ f.unop).obj _)

/-- The natural morphism from α^*_Q ⟶ α^ *_P  -/
@[simps]
def AlphaUpPQtoP : (AlphaUpStarP Q)⟶ (AlphaUpStarP P) where
  app _ := (AlphaUpFQtoP _ _ V_spec axiomP)
  naturality _ _ _ := by
    ext : 2
    apply colimit.hom_ext
    simp [AlphaUpFQtoP]

instance IsIsoAlphaUpPtoQ : IsIso (AlphaUpPQtoP V V_spec axiomP ):= by
  repeat
    apply ( NatTrans.isIso_iff_isIso_app _).2
    intro _

  rcases (isoQtoP _ _ hpq _ V_spec axiomP).out with ⟨i,hi⟩

  use i.hom
  constructor
  · calc _ = (QtoPhom _ _ _ _ _).hom ≫ i.hom := by simp
    _ = _ := by rw [← Cocone.category_comp_hom]
    _ = 𝟙 _ := by rw [hi.1] ;simp

  · calc _ = i.hom ≫ (QtoPhom _ _ _ _ _).hom := by simp
    _ = _ := by rw [← Cocone.category_comp_hom]
    _ = 𝟙 _ := by rw [hi.2] ;simp

def IsoAlphaUpPtoQ : (AlphaUpStarP Q) ≅ (AlphaUpStarP P):= by
  let h:= IsIsoAlphaUpPtoQ hpq V V_spec axiomP
  apply asIso (AlphaUpPQtoP V V_spec axiomP )

end

section --α^* variante avec seulement les U relativements comapcts


variable (X)
variable [LocallyCompactSpace X] [T2Space X]
--P

def relcCond : Opens X → Prop := fun (U:Opens X) => IsCompact (closure (U:Set X))
--Q
#check trueCond

def AlphaUpStarRc : ((Opens X)ᵒᵖ ⥤ Ab) ⥤ (Compacts X)ᵒᵖ ⥤ Ab := AlphaUpStarP (relcCond X)



lemma hpq : ∀ (U : Opens X), (relcCond X) U  → trueCond U := λ _ _ => rfl

lemma existsIntermed (h : K.carrier ⊆ U.carrier) : Nonempty ({ L //IsCompact L ∧ K.carrier ⊆ interior L ∧ L ⊆ U.carrier}) := by
  rcases (exists_compact_between K.isCompact U.isOpen h ) with ⟨L,hL⟩
  exact Nonempty.intro ⟨L,hL⟩

def V K : KsubU_cat K (trueCond) → KsubU_cat K (@relcCond X _):= by
  intro U
  let L:=(Classical.choice (existsIntermed X K U.obj U.property.1)).val
  use ⟨interior L,@isOpen_interior X L _⟩
  constructor
  · exact (Classical.choice (existsIntermed X K U.obj U.property.1)).property.2.1
  · apply IsCompact.of_isClosed_subset
    exact (Classical.choice (existsIntermed X K U.obj U.property.1)).property.1
    apply isClosed_closure
    intro _ ha
    apply ha
    constructor
    · apply IsCompact.isClosed
      exact (Classical.choice (existsIntermed X _ U.obj U.property.1)).property.1
    · apply interior_subset

lemma V_spec : ∀ K,∀ U, (V X K U).obj.carrier ⊆ U.obj:= by
  intro _ U
  unfold V
  apply Set.Subset.trans
  apply interior_subset
  exact (Classical.choice (existsIntermed X _ _ U.property.1)).property.2.2

lemma axiomP : ∀ U₁ U₂, relcCond X U₁ → relcCond X U₂ → relcCond X (U₁ ⊔ U₂):= by
  intro _ _ _ _
  unfold relcCond
  rw [ Opens.coe_sup, closure_union]
  apply IsCompact.union
  repeat assumption

def AlphaUpStarToRc : AlphaUpStar ≅ AlphaUpStarRc X:= by
  apply IsoAlphaUpPtoQ _ _ _ _
  exact λ _ _ => rfl
  exact V X
  exact (V_spec X)
  exact axiomP X

def AdjAlphaStarRc : AlphaUpStarRc X ⊣ AlphaDownStar := Adjunction.ofNatIsoLeft AdjAlphaStar (AlphaUpStarToRc X)

--#lint
