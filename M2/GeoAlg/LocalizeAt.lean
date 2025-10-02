import Mathlib

open CategoryTheory

#check AlgebraicGeometry.Scheme

variable {C: Type} [Category C] (J : Type ) [Quiver J]

variable (Top : GrothendieckTopology C)

structure localDataTop (j : J) where
  Da {D : J ⥤q C} {U : Sieve <| D.obj j} (hU : U ∈ Top (D.obj j)) {x : C} (i : @U x): J ⥤q C
  DajEqA {D : J ⥤q C} {U : Sieve <| D.obj j} {hU : U ∈ Top (D.obj j)} {x : C} (i : @U x) : (Da hU i).obj j = x

structure isLocalAt (P : (J ⥤q C) → Prop) (j : J) (loc: localDataTop J Top j) where
  iff_of_Top_covers (D : J ⥤q C) : P D ↔ ∀ U : Sieve (D.obj j), (hU : U ∈ Top (D.obj j)) → ∀ x : C, ∀ i : @U x,  P <| loc.Da hU i

variable (Aff: ObjectProperty C)

def A : Type := ObjectProperty.FullSubcategory Aff

instance : Category <| A Aff := CategoryTheory.ObjectProperty.FullSubcategory.category Aff





variable {A : Type} [Category A] (Spec : A ⥤ C)
class localData (j : J) where
  Da {a : A} {D : J ⥤q C} (i : Spec.obj a ⟶ D.obj j) : J ⥤q C
  DajEqA {a : A} {D : J ⥤q C} (i : Spec.obj a ⟶ D.obj j) : (Da i).obj j = Spec.obj a

variable [DecidableEq J]

--est-ce que ça reste def egal?
def localStd : localData J Spec j where
  Da {a D} i:= ⟨fun x => if decide (x = j) then Spec.obj a else D.obj x,
  fun {x y} f => by
    beta_reduce
    by_cases hx : x = j
    · suffices Spec.obj a ⟶ _ by
        apply Quiver.homOfEq this _ rfl
        simp
        intro hx2
        exact False.elim <| hx2 hx
      by_cases hy : y = j
      · apply Quiver.homOfEq (𝟙 _) rfl -- pas sur de l'idée sur 𝟙 _ mais en vrai ce cas ne devrais jamais arriver
        simp
        intro hy2
        exact False.elim <| hy2 hy
      · apply i ≫ _
        apply  Quiver.homOfEq (D.map f)
        · rw [hx]
        · simp
          intro hy2
          exact False.elim <| hy hy2
    · suffices D.obj x ⟶ _ by
        apply Quiver.homOfEq this _ rfl
        simp
        intro hx2
        exact False.elim <| hx hx2
      by_cases hy : y = j
      · suffices D.obj x ⟶ Spec.obj a by
          apply Quiver.homOfEq this rfl
          simp
          intro hy2
          exact False.elim <| hy2 hy
        -- la il faut faire un pullbakc mais ça impose de changer aussi la valeur de D.obj x


        sorry
      · apply Quiver.homOfEq (D.map f) rfl
        simp
        intro hy2
        exact False.elim <| hy hy2⟩
  DajEqA i := by simp -- ici il faudrait surement que rfl marche

  --example sur le quiver 0 -> 1 que l'on localise en 0 et en 1

def JEx : Type := Fin 2
instance QJEx : Quiver JEx := by
  exact { Hom := fun x y => if x.val = 0 ∧ y.val = 1 then Fin 1 else Fin 0}

def truc : @Quiver.Hom JEx QJEx ⟨0, by decide⟩ ⟨1, by decide⟩ := ⟨0,by decide⟩

def localAt0 : localData JEx Spec ⟨0,by decide⟩ where
  Da {a D} i := ⟨ fun x => if x.val = 0 then Spec.obj a else D.obj x,
    fun {x y} f => by
    by_cases h : x.val = 0 ∧ y.val = 1
    · let i2 : Spec.obj a ⟶ D.obj x := by
        apply Quiver.homOfEq i rfl
        apply congrArg D.obj
        apply Fin.eq_of_val_eq
        exact h.1.symm
      apply Quiver.homOfEq (i2 ≫ D.map f)
      · apply eq_ite_iff.2
        left
        exact ⟨h.1, rfl⟩
      · apply eq_ite_iff.2
        right
        exact ⟨by linarith, rfl⟩
    · simp only [Quiver.Hom, h, reduceIte] at f
      apply Fin.elim0 f⟩
  DajEqA {a d i} := by rfl

variable [Limits.HasPullbacks C]

noncomputable def localAt1 : localData JEx Spec ⟨1, by decide⟩ where
  Da{a D} i := ⟨ fun x => if x.val = 0 then
    Limits.pullback (D.map truc) i else Spec.obj a,
    fun {x y} f => by
    by_cases h : x.val = 0 ∧ y.val = 1
    · apply Quiver.homOfEq (Limits.pullback.snd (D.map truc) i)
      · apply eq_ite_iff.2
        left
        exact ⟨h.1, rfl⟩
      · apply eq_ite_iff.2
        right
        exact ⟨ by linarith, rfl⟩
    · simp only [Quiver.Hom, h, reduceIte] at f
      apply Fin.elim0 f⟩
  DajEqA {a d i} := by rfl
