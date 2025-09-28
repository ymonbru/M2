import Mathlib

open CategoryTheory

#check AlgebraicGeometry.Scheme

variable (C: Type) [Category C] (A : Type) [Category A] (Spec : A ⥤ C) (J : Type ) [Quiver J] (P : (J ⥤q C) → Prop) (j : J)

variable (a : A) (D : J ⥤q C)

structure localData (j : J) where
  Da {a : A} {D : J ⥤q C} (i : Spec.obj a ⟶ D.obj j) : J ⥤q C
  DajEqA {a : A} {D : J ⥤q C} (i : Spec.obj a ⟶ D.obj j) : (Da i).obj j = Spec.obj a

variable [DecidableEq J]

--est-ce que ça reste def egal?
def localStd : localData C A Spec J j where
  Da {a D} i:= ⟨fun x => if x = j then Spec.obj a else D.obj x,
  fun {x y} f => by
    beta_reduce
    by_cases hx : x = j
    · suffices Spec.obj a ⟶ _ by
        apply Quiver.homOfEq this _ rfl
        simp only [left_eq_ite_iff]
        intro hx2
        exact False.elim <| hx2 hx
      by_cases hy : y = j
      · apply Quiver.homOfEq (𝟙 _) rfl -- pas sur de l'idée sur 𝟙 _ mais en vrai ce cas ne devrais jamais arriver
        simp only [left_eq_ite_iff]
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
      sorry
      sorry⟩
  DajEqA i := by simp
--example sur le quiver 1 -> 2 que l'on localise en 1

def JEx : Type := Fin 2
instance QJEx : Quiver JEx := by
  exact { Hom := fun x y => if x.val = 0 && y.val =1 then Fin 1 else Fin 0}

def localAt1 : localData C A Spec JEx ⟨0,by decide⟩   where
  Da {a D} i := ⟨ fun x => if x.val = 0 then Spec.obj a else D.obj x,
    by
    intro x y f
    by_cases hx : x.val = 0
    by_cases hy : y.val = 0
    · simp [Quiver.Hom, hy] at f
      exact Fin.elim0 f
    · apply Quiver.homOfEq  (_ ≫ (D.map f)) (rfl)
      · simp
        intro hy2
        exact False.elim (hy (Fin.val_eq_zero_iff.mpr hy2))
      · apply Quiver.homOfEq i
        · simp
          intro hx2
          exact False.elim (hx2 (Eq.symm (Fin.eq_of_val_eq (id (Eq.symm hx)))))
        · congr
          repeat exact hx.symm
    · simp [Quiver.Hom, hx] at f
      exact Fin.elim0 f⟩
  DajEqA {a d i} := by simp


--def isLocalAt : Prop := ∀
