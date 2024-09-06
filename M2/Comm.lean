variable (hom:Type) [DecidableEq hom] (andThen: hom → hom → hom)

variable (obj:Type) (dom codom: hom → obj)


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
def applyTriangle (t:triangle hom andThen) (c:List hom ): Bool × List hom := match c with
  |[] => (true,c)
  |_ :: [] => (true,c)
  |a :: b :: cprime =>
    if a = t.f ∧ b = t.g then (false,t.h :: cprime)
    else let (b,newc):= applyTriangle t (b::cprime)
      (b,a::newc)


def applyListTriangles (lt:List (triangle hom andThen)) (c:List hom ):List (triangle hom andThen)× List hom :=
  match lt with
    |[] => ([],c)
    |t::ltprime => let (b,newc) := applyTriangle hom andThen t c
      let (newlt,newc) := applyListTriangles ltprime newc
      if b then (t::newlt,newc)
      else (newlt,newc)

def expandTriangle (ok:Bool) (t:triangle hom andThen) (c:List hom ): Bool × List hom :=
  if not ok then (false,c)
  else  match c with
    |[] => (ok,c)
    |a :: cprime =>
      if  t.h = a then (false,t.f :: t.g :: cprime)
      else (ok, a :: (expandTriangle  ok t cprime).2)

def expandOneTriangle (lt:List (triangle hom andThen)) (c:List hom ): List (triangle hom andThen)× List hom := match lt with
  |[]=> (lt,c)
  |t :: ltprime =>
    let (b,newc):= expandTriangle hom andThen true t c
    if b then let (ltprime,newc):=expandOneTriangle ltprime c
      (t::ltprime,newc)
    else (ltprime,newc)
