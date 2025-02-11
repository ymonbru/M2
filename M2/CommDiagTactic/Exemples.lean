import M2.CommDiagTactic.FindPath
--import Egg

open CategoryTheory

set_option trace.profiler true


variable (Cat : Type ) [Category Cat]

variable (A B C D E F G H : Cat) (a : A ⟶ D) (b : A ⟶ C) (c : A ⟶ B) (d : B ⟶ C) (e : C ⟶ E) (f : B ⟶ F) (h : F ⟶ E) (i : E ⟶ G) (j : D ⟶ G) (k : F ⟶ G) (l : G ⟶ H) (m : B ⟶ G) (n : B ⟶ H)

lemma test (h1 : c ≫ d = b) (h2 : b ≫ e = a ≫ g) (h3 : d ≫ e = f ≫ h) (h4 : g ≫ i = j) (h5 : h ≫ i = k) (h6 : f ≫ k = m ) (h7 : m ≫ l = n) : a ≫ j ≫ l = c ≫ n:= by
    findPath


variable (a : A ⟶ B) (b : A ⟶ C) (c : B ⟶ C) (d : B ⟶ D) (e : D ⟶ C) (f : C ⟶ E) (g : D ⟶ E) (h : E ⟶ F) (i : D ⟶ F) (j : D ⟶ G) (k : F ⟶ G) (l : E ⟶ G)

-- (h6 : h ≫ k = l )
lemma test2  (h1 : a ≫ c  = b) (h2 : d ≫ e = c) (h3 : e ≫ f = g) (h4 : g ≫ h = i) (h5 :  i ≫ k = j ) : a ≫  d ≫ j = b ≫ f ≫ h ≫ k := by
  findPath

variable (a : A ⟶ B) (b : B ⟶ D) (c : C ⟶ D) (d: A ⟶ C) (e: C ⟶ B)

lemma test3 (h1 : d ≫ e = a) (h2 : e ≫ b = c): a ≫ b = d ≫ c := by
  findPath


variable (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ D) (d: D ⟶ C) (e: A ⟶ E) (f: E ⟶ C) (g: A ⟶ C)


lemma test4 (h1 : a ≫ b = g)  (h2 : c ≫ d = g) (h3: e ≫ f = g) : a ≫ b = c ≫ d := by
  findPath

variable (a:A ⟶ B) (b: B ⟶ C) (y : A ⟶ C) (c d : C ⟶ D)

--lemma test567 (h1: a≫ b = y) : y ≫ c= y ≫ d := by sorry

variable (a ap: A ⟶ B) (b bp: B ⟶ C ) (x xp : A ⟶ C) (y yp : B ⟶ D) (c cp d  : C ⟶ D)

lemma test12 (h1 : a ≫ b = x) (h2 : ap ≫ bp =x) (h3: b ≫ c =y) (h4 : bp ≫ cp = yp) (h5 : b ≫ d = y) (h6 : bp ≫ d = yp ) : a ≫ b ≫ c = ap ≫ bp ≫ cp := by
    findPath


/-https://q.uiver.app/#q=WzAsNCxbMCwwLCJBIl0sWzIsMCwiQiJdLFsyLDIsIkMiXSxbNCwwLCJEIl0sWzAsMSwiYSIsMV0sWzEsMiwiYiIsMV0sWzAsMSwiYSciLDEseyJjdXJ2ZSI6LTJ9XSxbMSwyLCJiJyIsMSx7ImN1cnZlIjotMn1dLFswLDIsIngiLDEseyJjdXJ2ZSI6Mn1dLFswLDIsIngnIiwxLHsiY3VydmUiOjV9XSxbMSwzLCJ5IiwxXSxbMSwzLCJ5JyIsMSx7ImN1cnZlIjotMn1dLFsyLDMsImQiLDFdLFsyLDMsImMiLDEseyJjdXJ2ZSI6Mn1dLFsyLDMsImMnIiwxLHsiY3VydmUiOjV9XV0=-/

lemma test5 (h1 : a ≫ b = g)  (h3: e ≫ f = g) : a ≫ b = a ≫ b := by
  findPath

lemma test6  : a ≫ b = a ≫ b := by
  findPath

variable (a: A ⟶ B) (b : A ⟶ C) (c: B ⟶ C) (d e x: B⟶ D) (f: D ⟶ C) (g: D ⟶ E) (h i y : C ⟶ E)

lemma test7  (h1 : b = a ≫ c) (h2 : f ≫ h = g) (h3 : f ≫ i = g) (h4 : d ≫ f = c)
(h5 : e ≫ f = c ) (h6 : x ≫ f = c) (h7 : f ≫ y = g): a ≫ c ≫ y= a ≫ c ≫ i := by
    findPath


variable (A B C D : Cat)
variable (x : A ⟶ B) (y u : B ⟶ C) (z : A ⟶ C) (b : B ⟶ D) (a : C ⟶ D)

lemma test8 (h1 : x ≫ y = z) (h2: b = u ≫ a) (h3 : y ≫ a = b) (h4 : z = x ≫ u): x ≫ y ≫ a = x ≫ u ≫ a := by
  findPath

variable (A B C D E F G H I : Cat)
variable (x : B ⟶ C) (y : A ⟶ C) (a : A ⟶ B) (b : C ⟶ D) (c : B ⟶ D) (d : D ⟶ E) (e : A ⟶ D) (f : A ⟶ E) (g : C ⟶ E) (xp : F ⟶ G) (yp : E ⟶ G) (ap : E ⟶ F) (bp : G ⟶ H) (cp : F ⟶ H) (dp : H ⟶ I) (ep : E ⟶ H) (fp : E ⟶ I) (gp : G ⟶ I)

lemma test9 (h1 : a ≫ x = y) (h2 : x ≫ b = c) (h3 : a ≫ c = e)
(h4 : e ≫ d = f) (h5 : y ≫ g = f) (h6 : ap ≫ xp = yp) (h7 : xp ≫ bp = cp) (h8 : ap ≫ cp = ep) (h9 : ep ≫ dp = fp) (h10 : yp ≫ gp = fp) : a ≫ x ≫ b ≫ d ≫ ap ≫ xp ≫ gp = a ≫ x ≫ g ≫ ap ≫ xp ≫ bp ≫ dp := by
  findPath

--https://q.uiver.app/#q=WzAsOSxbMCw0LCJBIl0sWzIsNCwiQiJdLFszLDYsIkMiXSxbMywzLCJEIl0sWzQsMiwiRSJdLFs2LDIsIkYiXSxbNyw0LCJHIl0sWzcsMSwiSCJdLFs4LDAsIkkiXSxbMCwxLCJhIiwxXSxbMSwyLCJ4IiwxXSxbMiwzLCJiIiwxXSxbMyw0LCJkIiwxXSxbMCwyLCJ5IiwxXSxbMSwzLCJjIiwxXSxbMCwzLCJlIiwxXSxbMCw0LCJmIiwxXSxbMiw0LCJnIiwxXSxbNCw1LCJhJyIsMV0sWzQsNiwieSciLDFdLFs1LDYsIngnIiwxXSxbNiw3LCJiJyIsMV0sWzUsNywiYyciLDFdLFs0LDcsImUnIiwxXSxbNyw4LCJkJyIsMV0sWzQsOCwiZiciLDFdLFs2LDgsImcnIiwxXV0=

lemma test10 (h1 : a ≫ x = y) (h2 : x ≫ b = c) (h3 : a ≫ c = e)
(h4 : e ≫ d = f) (h5 : y ≫ g = f) : a ≫ x ≫ b ≫ d = a ≫ x ≫ g := by
  findPath

variable (A B C D E F G : Cat)
variable (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (d : D ⟶ E) (e : E ⟶ F) (x: A ⟶ C) (xp: A ⟶ G) (y : C ⟶ E) (yp : G ⟶ F) (u : B ⟶ G) (v : G ⟶ E)


lemma test11 (h1 : a ≫ b = x) (h2 : b ≫ y = u ≫ v) (h3 : y = c ≫ d) (h4 : a ≫ u = xp) (h5 : v ≫ e = yp) : a ≫ b ≫ c ≫ d ≫ e = a ≫ u ≫ yp := by
  findPath

--https://q.uiver.app/#q=WzAsMTUsWzAsMSwiQSJdLFsyLDEsIkIiXSxbMywwLCJDIl0sWzUsMCwiRCJdLFs0LDEsIkUiXSxbNSwyLCJGIl0sWzMsMiwiRyJdLFs3LDAsImFiY2RlIl0sWzksMCwiYWJ5ZSJdLFs3LDIsInhjZGUiXSxbOSwyLCJ4eWUiXSxbMTEsMCwiYXV2ZSJdLFsxMSwyLCJ4J3ZlIl0sWzEzLDIsIngneSciXSxbMTMsMCwiYXV5JyJdLFswLDEsImEiLDFdLFsxLDIsImIiLDFdLFswLDIsIngiLDFdLFsyLDMsImMiLDFdLFszLDQsImQiLDFdLFsyLDQsInkiLDFdLFs0LDUsImUiLDFdLFsxLDYsInUiLDFdLFs2LDQsInYiLDFdLFswLDYsIngnIiwxXSxbNiw1LCJ5JyIsMV0sWzcsOCwiMyIsMV0sWzcsOSwiMSIsMV0sWzksMTAsIjMiLDFdLFs4LDEwLCIxIiwxXSxbOCwxMSwiMiIsMV0sWzExLDEyLCI0IiwxXSxbMTIsMTMsIjUiLDFdLFsxMSwxNCwiNSIsMV0sWzE0LDEzLCI0IiwxXV0=
