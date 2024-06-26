import Mathlib
import Mathlib.Topology.Separation

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Compacts Opposite

variable (X) [TopologicalSpace X] [T2Space X]
variable (K:Compacts X)
variable (F:(Compacts X)ᵒᵖ ⥤ Ab) (K₁:Compacts X) (K₂:Compacts X)


-- Les deux déclarations suivantes doivent être munies de vraies docstrings (on doit les voir
-- quand on met la souris dessus. Tu dois pouvoir taper #lint à la fin du fichier sans protestation.

-- Il ne faut pas utiliser `Opens.carrier`. Ce n’est pas la forme normale retenue par Mathlib.
-- Les lemmes, en particulier ceux marqués `simp` attendent la coercion. Cette coercion est
-- `Open.carrier` modulo définitions mais pas syntaxiquement donc `rw` et `simp` ne fonctionneront pas.

--La limite
def RelCN : Set (Opens X) := fun (U:Opens X) ↦ (K.carrier ⊆ U.carrier) ∧ IsCompact (closure U : Set X)

def RelCN_cat : Type := FullSubcategory (RelCN X K)

instance : Category (RelCN_cat X K) := FullSubcategory.category (RelCN X K)

--surement déjà dans mathlib mais exo
lemma closure_increasing (U:Set X) (V:Set X) (h: U ⊆ V): closure U ⊆ closure V:= by
  -- apply? fait l’exo
  intros a ha W hW
  unfold closure at ha
  simp [Set.mem_iInter] at ha
  apply ha _ hW.1
  exact Set.Subset.trans h hW.2

-- la ligne suivante demande à Lean de t’aider à écrire les indispensable lemmes simp.
-- Essaie avec `@[simps?]` pour voir les lemmes crées.
@[simps]
def closureFunc : RelCN_cat X K ⥤ Compacts X  where
  obj U := ⟨closure U.obj, U.property.2⟩
  map f :=  homOfLE (closure_increasing _ _ _ (leOfHom f))
                                        -- tous ces _ suggèrent un problème de () vs {}

@[simps!]
def FUbar : (RelCN_cat X K)ᵒᵖ ⥤ Ab := (closureFunc X K).op.comp  F


-- Je ne comprends pas pourquoi Lean affiche tous les `op K` comme `{unop := K}' qui est horrible
-- à lire. Il faudrait poser la questions sur Zulip. En attendant, on va lui forcer la main
-- avec un `app_unexpander`.
@[app_unexpander Opposite.op]
def unexpandOp : Lean.PrettyPrinter.Unexpander
  | `($_ $x:term) => `($(Lean.mkIdent `op) $x) -- Ce `Lean.mkIdent` est un hack honteux.
  | _ => throw ()

def FK_transNat : FUbar X K F ⟶ (Functor.const (RelCN_cat X K)ᵒᵖ).obj (op K) |>.comp F where
  -- Il est préférable de réserver les tactiques aux démonstration et pas aux constructions
  -- de données même si ici ça ne change rien
  app W:= F.map <| op <| homOfLE <| by
    apply (W.unop).property.1.trans
    simp [subset_closure]
  naturality := by
    intros W Y f
    -- On évite les simp non terminaux pour la maintenance
    suffices F.map (homOfLE _).op ≫ F.map (op <| homOfLE _) = F.map (op <| homOfLE _) by simpa
    rw [← F.map_comp]
    rfl

def FK : Cocone (FUbar X K F) :=
  .mk (F.obj (op K)) (FK_transNat X K F  ≫ (Functor.constComp _ _ _).hom)

--Le complexe à 4 terme

open ZeroObject
noncomputable section

-- Cela fera sans doute bugger des fichiers ultérieurs mais X n’a rien à faire comme argument
-- explicite dans cette section
variable {X}

-- Dans cette section, indiquer le type des définitions est vraiment plus agréable pour les
-- êtres humains
-- Les notations sont importantes aussi, surtout si tu laisses Lean élider complètement
-- les arguments propositionnels et afficher `homOfLe ⋯` partout
-- Note que dans ce cas
-- set_option pp.proofs.withType true
-- peut être très utile

def toSupLeft : op (K₁ ⊔ K₂) ⟶ op K₁ := opHomOfLE le_sup_left
def toSupRight : op (K₁ ⊔ K₂) ⟶ op K₂ := opHomOfLE le_sup_right

def fromInfLeft : op K₁ ⟶ op (K₁ ⊓ K₂) := opHomOfLE inf_le_left
def fromInfRight : op K₂ ⟶ op (K₁ ⊓ K₂) := opHomOfLE inf_le_right

@[simp]
lemma toSupLeft_comp_fromInf_left : toSupLeft K₁ K₂ ≫ fromInfLeft K₁ K₂ = opHomOfLE inf_le_sup :=
  rfl

@[simp]
lemma toSupRight_comp_fromInf_rigt : toSupRight K₁ K₂ ≫ fromInfRight K₁ K₂ = opHomOfLE inf_le_sup :=
  rfl

def ZtoFcup : 0 ⟶ F.obj <| op (K₁ ⊔ K₂) := 0 -- 0 -> F(K₁ ∪ K₂)

def FcuptoplusF : F.obj (op (K₁ ⊔ K₂)) ⟶ F.obj (op K₁) ⊞ F.obj (op K₂) :=
  F.map (toSupLeft  K₁ K₂) ≫ biprod.inl +
  F.map (toSupRight K₁ K₂) ≫ biprod.inr

def plusFtoFcap : F.obj (op K₁) ⊞ F.obj (op K₂) ⟶ F.obj (op (K₁ ⊓ K₂)) :=
  biprod.fst ≫ F.map (fromInfLeft  K₁ K₂) -
  biprod.snd ≫ F.map (fromInfRight K₁ K₂)

def complex : ComposableArrows Ab 3 :=
  .mk₃ (ZtoFcup F K₁ K₂) (FcuptoplusF F K₁ K₂) (plusFtoFcap F K₁ K₂)

-- Chercher simprocs dans le fichier CategoryTheory/ComposableArrows.lean
instance : (complex F K₁ K₂).IsComplex where
  zero := by
    intros i hi
    unfold complex ZtoFcup FcuptoplusF plusFtoFcap
    have hi' : i ≤ 1 := by simpa using hi
    set_option simprocs false in
    interval_cases i
    · -- F(K₁ ∪ K₂)-> F(K₁) ⊞ F(K₂)-> F(K₁) ⊞ F(K₂)-> F(K₁ ∩ K₂)=0
      simp
    · -- 0 -> F(K₁ ∪ K₂) -> F(K₁ ∪ K₂)-> F(K₁) ⊞ F(K₂)=0
      simp [← F.map_comp]


variable (X)

-- Es-tu sûr que tous ces `aesop_cat` ont une chance de fonctionner ? Sinon ils ne font que ralentir
-- et embrouiller

@[ext]
structure Ksheaf where
  carrier : (Compacts X)ᵒᵖ ⥤ Ab
  ksh1 : carrier.obj (op (⊥ : Compacts X)) = 0 := by aesop_cat
  ksh2 : ∀ K₁ K₂ : Compacts X, (complex carrier K₁ K₂).Exact := by aesop_cat
  ksh3 : ∀ K : Compacts X, (IsIso (colimit.desc (FUbar X K carrier) (FK X K carrier))) := by aesop_cat

instance : Category (Ksheaf X) := InducedCategory.category (·.carrier)

#check (inducedFunctor fun F : Ksheaf X ↦ F.carrier : Ksheaf X ⥤ _)
