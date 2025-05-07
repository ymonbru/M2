import Mathlib




class myQuiver (V : Type ) where
  Hom : V → V → Sort

class myCategoryStruct (obj : Type ) : Type  extends myQuiver obj where
  /-- The identity morphism on an object. -/
  id : ∀ X : obj, Hom X X
  /-- Composition of morphisms in a category, written `f ≫ g`. -/
  comp : ∀ {X Y Z : obj}, (Hom X Y) → (Hom Y Z) → (Hom X Z)

class myCategory (obj : Type ) : Type  extends myCategoryStruct obj where
  id_comp : ∀ {X Y : obj} (f : Hom X Y), (comp (id X)  f ) = f := by aesop_cat
  comp_id : ∀ {X Y : obj} (f : Hom X Y), comp f  (id Y) = f := by aesop_cat
  /-- Composition in a category is associative. -/
  assoc : ∀ {W X Y Z : obj} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z), comp (comp f g) h = comp f (comp g h) := by
    aesop_cat


structure myPrefunctor (V : Type ) [myQuiver V] (W : Type) [myQuiver W] where
  /-- The action of a (pre)functor on vertices/objects. -/
  obj : V → W
  /-- The action of a (pre)functor on edges/arrows/morphisms. -/
  map : ∀ {X Y : V}, (myQuiver.Hom X Y) → (myQuiver.Hom (obj X) (obj Y))




structure myFunctor (C : Type ) [myCategory C] (D : Type ) [myCategory D] :
    Type
    extends myPrefunctor C D where
  /-- A functor preserves identity morphisms. -/
  map_id : ∀ X : C, map (myCategoryStruct.id X) = myCategoryStruct.id (obj X) := by aesop_cat
  /-- A functor preserves composition. -/
  map_comp : ∀ {X Y Z : C} (f : myQuiver.Hom X Y) (g : myQuiver.Hom Y  Z), map (myCategoryStruct.comp f g) = myCategoryStruct.comp (map f)  (map g) := by aesop_cat


variable (C D: Type) [myCategory C] [myCategory D]


def myEqToHom {X Y : C} (p : X = Y) : myQuiver.Hom X Y := by
  rw [p]
  exact myCategoryStruct.id Y



theorem myExt {F G : myFunctor C D} (h_obj : ∀ X, F.obj X = G.obj X)
    (h_map : ∀ X Y f,
      F.map f =  myCategoryStruct.comp (myEqToHom D (h_obj X)) (myCategoryStruct.comp (G.map f) (myEqToHom D (h_obj Y).symm)) := by aesop_cat) :
    F = G := by
      match F, G with
        | myFunctor.mk F_pre _ _ , myFunctor.mk G_pre _ _ =>
          match F_pre, G_pre with
            | myPrefunctor.mk F_obj _ , myPrefunctor.mk G_obj _ =>
              obtain rfl : F_obj = G_obj := by
                ext X
                apply h_obj
              congr
              --funext X Y f
              --simpa using h_map X Y f


theorem myCongr_obj {F G : myPrefunctor C D} (h : F = G) (X) : F.obj X = G.obj X := by rw [h]


theorem myCongr_hom {F G : myPrefunctor C D} (h : F = G) {X Y: C} (f :myQuiver.Hom X Y) :
    F.map f = myCategoryStruct.comp (myEqToHom D (myCongr_obj C D h X)) (myCategoryStruct.comp (G.map f) (myEqToHom D (myCongr_obj C D h Y).symm)) := by
  subst h; simp

variable (G : myFunctor C C)

lemma truc1 : G = G := by
  apply myExt

  intro U V f
  apply myCongr_hom


open CategoryTheory

variable (B : Type ) [CategoryTheory.Category B]

variable (G : B ⥤ B)


lemma truc : G = G := by
  apply CategoryTheory.Functor.ext --(h_map := ?_)
  --sorry
  intro U V f
  apply Functor.congr_hom
