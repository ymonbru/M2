import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v
variable {C : Type u} [Category.{v,u} C] (F G : WalkingCospan ⥤ C)

/--An helper to buil natural transformation between functors WalkingCospan ⥤ C. In particular it makes obvious for simp the naturality case for id, wich simp cant close in some particular cases-/
@[simps]
def natTransWcspFunc (fL: F.obj .left ⟶ G.obj .left)(fR: F.obj .right ⟶ G.obj .right) (fO: F.obj .one ⟶ G.obj .one) (hOL : F.map WalkingCospan.Hom.inl ≫ fO = fL ≫ G.map WalkingCospan.Hom.inl) (hOR : F.map WalkingCospan.Hom.inr ≫ fO = fR ≫ G.map WalkingCospan.Hom.inr) : F ⟶ G where
  app x:= match x with
    |.left => fL
    |.right => fR
    |.one => fO
  naturality x y f := match f with
    | WalkingCospan.Hom.inl => hOL
    | WalkingCospan.Hom.inr => hOR
    | WalkingCospan.Hom.id _ => by simp

/-- The specialisation of natTransWcspFunc in the case where the functors are obtain by cospan-/
@[simps!]
def natTransCospan {C : Type u} [Category.{v} C] { A1 B1 C1 A2 B2 C2 : C} { f1 : A1 ⟶ B1} { g1 : C1 ⟶ B1} { f2 : A2 ⟶ B2} { g2 : C2 ⟶ B2} (a : A1 ⟶ A2) (b : B1 ⟶ B2) (c : C1 ⟶ C2) (hab : f1 ≫ b = a ≫ f2) (hbc : g1 ≫ b = c ≫ g2):  cospan f1 g1 ⟶ cospan f2 g2 :=  natTransWcspFunc (cospan f1 g1) _ a c b hab hbc


/-- Build isomorphism between two natural transformations between functors : Walkingcospan ⥤ C (build with natTransWcspFunc) by prooving only once the compatibility condition-/
@[simps]
def IsoWcspFunc {C : Type u} [Category.{v} C] (F G : WalkingCospan ⥤ C) (fL: F.obj .left ≅ G.obj .left)(fR: F.obj .right ≅ G.obj .right) (fO: F.obj .one ≅ G.obj .one) (hOL : F.map WalkingCospan.Hom.inl ≫ fO.hom = fL.hom ≫ G.map WalkingCospan.Hom.inl) (hOR : F.map WalkingCospan.Hom.inr ≫ fO.hom = fR.hom ≫ G.map WalkingCospan.Hom.inr) : F ≅ G where
  hom := natTransWcspFunc F G fL.hom fR.hom fO.hom hOL hOR
  inv := by
    refine natTransWcspFunc _ _ fL.inv fR.inv fO.inv ?_ ?_
    · calc _ = fL.inv ≫ (fL.hom ≫ G.map WalkingCospan.Hom.inl) ≫ fO.inv := by simp
           _ = fL.inv ≫ F.map WalkingCospan.Hom.inl ≫ fO.hom ≫ fO.inv:= by simp [← hOL]
            _ = _ := by simp
    · calc _ = fR.inv ≫ (fR.hom ≫ G.map WalkingCospan.Hom.inr) ≫ fO.inv := by simp
           _ = fR.inv ≫ F.map WalkingCospan.Hom.inr ≫ fO.hom ≫ fO.inv:= by simp [← hOR]
            _ = _ := by simp
