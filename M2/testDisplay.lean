import M2.FindPath
import Mathlib.ProofWidgets.Component.GraphDisplay
import Mathlib.ProofWidgets.Component.HtmlDisplay

--https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2Fleanprover-community%2FProofWidgets4%2Frefs%2Fheads%2Fmain%2FProofWidgets%2FDemos%2FGraph.lean
open ProofWidgets Jsx

/-! ### Basic usage -/

def mkEdge (st : String × String) : GraphDisplay.Edge := {source := st.1, target := st.2}

open CategoryTheory

variable (Cat : Type ) [Category Cat]

variable (A B C D E F G H : Cat) (a : A ⟶ D) (b : A ⟶ C) (c : A ⟶ B) (d : B ⟶ C) (e : C ⟶ E) (f : B ⟶ F) (h : F ⟶ E) (i : E ⟶ G) (j : D ⟶ G) (k : F ⟶ G) (l : G ⟶ H) (m : B ⟶ G) (n : B ⟶ H)

lemma ex (h1 : c ≫ d = b) (h2 : b ≫ e = a ≫ g) (h3 : d ≫ e = f ≫ h) (h4 : g ≫ i = j) (h5 : h ≫ i = k) (h6 : f ≫ k = m ) (h7 : m ≫ l = n) : a ≫ j ≫ l = c ≫ n:= by
  /-split_square

  rw [← h7, ← h6, ← h5,]
  rw_assoc2 h3.map_eq_right
  rw [← h3.map_eq_left]
  rw_assoc2 h1
  rw_assoc2 h2.map_eq_left
  rw[← h2.map_eq_right]
  rw_assoc h4

  repeat rw [Category.assoc]-/

  FindPath
