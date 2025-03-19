import Mathlib.CategoryTheory.Limits.Shapes.Terminal

open CategoryTheory Limits

noncomputable section

variable {C A} [Category C] [Category A] {T : C} (hT: IsTerminal T)
variable (F: C ⥤ A)

@[simps]
def FTopι : F ⟶ (Functor.const C).obj (F.obj T) where
  app U:= F.map <| IsTerminal.from hT U
  naturality U V i := by
    simp [← F.map_comp]

@[simps]
def FTop : Cocone F where
  pt := (F).obj T
  ι := FTopι hT F

def FTopCoconeCoLimit : IsColimit (FTop hT F) where
  desc s := s.ι.app _
  uniq s m hj:= by
    simp [← (hj T)]

end

noncomputable section

variable {C A} [Category C] [Category A] {I : C} (hI: IsInitial I)
variable (F: C ⥤ A)


@[simps]
def FBotι : (Functor.const C).obj (F.obj I) ⟶ F where
  app U:= F.map <| IsInitial.to hI U
  naturality U V i := by
    simp [← F.map_comp]

@[simps]
def FBot : Cone F where
  pt := (F).obj I
  π := FBotι hI F

def FBotConeLimit : IsLimit (FBot hI F) where
  lift s := s.π.app _
  uniq s m hj:= by
    simp [← (hj I)]

end
