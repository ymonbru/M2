variable {hom:Type} [DecidableEq hom] (andThen: hom → hom → hom)

variable {obj:Type} (dom codom: hom → obj)

@[ext]
structure triangle where--f≫ g=h
  f: hom
  g: hom
  h: hom
  trg_com: andThen f g = h



--variable (Chemin1 Chemin2: List hom)
--variable (Rules : List (triangle hom andThen))
--variable (t:triangle hom andThen)

--#check t.f


-- le booléen est à true si on n'a rien changé et false si on à modifié un truc
def applyTriangle (t:triangle andThen) (c:List hom ): Bool × List hom := match c with
  |[] => (true,c)
  |_ :: [] => (true,c)
  |a :: b :: cprime =>
    if a = t.f ∧ b = t.g then (false,t.h :: cprime)
    else let (b,newc):= applyTriangle t (b::cprime)
      (b,a::newc)

-- le booléen est à true si on n'a rien changé et false si on à modifié un truc
def applyListTriangles (lt:List (triangle andThen)) (c:List hom ):Bool × List (triangle andThen) × List hom :=
  match lt with
    |[] => (true,[],c)
    |t::ltprime => let (b,newc) := applyTriangle andThen t c
      let (newbool,newlt,newc) := applyListTriangles ltprime newc
      if b then (true, t::newlt,newc)
      else (newbool, newlt,newc)

-- le booléen est à true si on n'a rien changé et false si on à modifié un truc
def expandTriangle (ok:Bool) (t:triangle andThen) (c:List hom ): Bool × List hom :=
  if not ok then (false,c)
  else  match c with
    |[] => (ok,c)
    |a :: cprime =>
      if  t.h = a then (false,t.f :: t.g :: cprime)
      else (ok, a :: (expandTriangle  ok t cprime).2)

-- le booléen est à true si on n'a rien changé et false si on à modifié un truc
def expandOneTriangle (lt:List (triangle andThen)) (c:List hom ): Bool × List (triangle andThen)× List hom := match lt with
  |[]=> (true,lt,c)
  |t :: ltprime =>
    let (b,newc):= expandTriangle andThen true t c
    if b then let (newbool,ltprime,newc):=expandOneTriangle ltprime c
      (newbool,t::ltprime,newc)
    else (true,ltprime,newc)

def IsValid (l:List hom): Prop:= match l with
  |[]=> True
  |_ :: [] => True
  |f :: g :: lprime => (codom f = dom g) ∧ (IsValid (g :: lprime))

partial def CommDiag (lt:List (triangle andThen)) (l : List hom ): List hom:=
  let (_,newlt,newl) := applyListTriangles andThen lt l
  let (newb,newt,newl) := expandOneTriangle andThen newlt newl

  if not newb then
    CommDiag newt newl
  else newl

variable (a b c d e: Nat)

def t: triangle Nat.add where
  f := a
  g := b
  h := c
  trg_com := sorry


#eval t 1 2 3

def lt : List (triangle Nat.add):= (t 1 3 2) :: (t  3 4 5) :: List.nil

def l : List Nat := 1 :: 5 :: List.nil

#check lt

#eval CommDiag Nat.add lt l
