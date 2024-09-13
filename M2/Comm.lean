variable {hom:Type} [DecidableEq hom] (andThen: hom → hom → hom)

variable {obj:Type} (dom codom: hom → obj)

@[ext]
structure triangle where--f≫ g=h
  f: hom
  g: hom
  h: hom
  trg_com: andThen f g = h
deriving Repr

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
      --dite (t.h=a) (false,t.f :: t.g :: cprime) (let (newok,newc):= expandTriangle  ok t cprime;
      --  (newok,a::newc))
      if  (t.h = a) then (false,t.f :: t.g :: cprime)
      else let (newok,newc):= expandTriangle  ok t cprime
        (newok,a::newc)

-- le booléen est à true si on n'a rien changé et false si on à modifié un truc
def expandOneTriangle (lt:List (triangle andThen)) (c:List hom ): Bool × List (triangle andThen)× List hom := match lt with
  |[]=> (true,lt,c)
  |t :: ltprime =>
    let (b,newc):= expandTriangle andThen true t c
    if b then let (newbool,ltprimeprime,newnewc):= expandOneTriangle ltprime c
      (newbool, t::ltprimeprime, newnewc)
    else (false,ltprime,newc)


def IsValid (l:List hom): Prop:= match l with
  |[]=> True
  |_ :: [] => True
  |f :: g :: lprime => (codom f = dom g) ∧ (IsValid (g :: lprime))

partial def CommDiag (lt:List (triangle andThen)) (l : List hom ): List hom:=
  let (_, newlt, newl) := applyListTriangles andThen lt l
  let (newb, newt, newl) := expandOneTriangle andThen newlt newl

  if not newb then
    CommDiag newt newl
  else newl
--termination_by sizeOf l + sizeOf lt
variable (a b c d e: Nat)

def t: triangle Nat.add where
  f := a
  g := b
  h := c
  trg_com := sorry


#eval t 1 2 3

def lt : List (triangle Nat.add):= (t 1 3 2) :: (t 3 4 5) :: List.nil

def l : List Nat := 1 :: 5 :: List.nil

#eval lt

#eval applyListTriangles Nat.add lt [1,3,4]

#eval expandOneTriangle Nat.add lt l

#eval CommDiag Nat.add lt l

variable (id: hom)

def comp (c: List hom): hom := match c with
  |[] => id --on aimerait s'en passer mais ça introduit une disjonction de cas penible dans la preuve de composition qui suit
  |t::q => andThen t (comp q)


variable {andThenAssoc: ∀ f g h, andThen f (andThen g h)= andThen (andThen f g) h}
variable {idNeutral: ∀ f, andThen f id = f}


theorem diagIsComApplyT (t : triangle andThen) (lh : List hom): comp andThen id lh = comp andThen id (applyTriangle andThen t lh).2 := by
  induction lh with
  | nil =>
    rw [comp,applyTriangle,comp]
  |cons f q hr =>
    match q with
    | [] =>
      rw [applyTriangle]
    | g :: qq  =>
      rw [comp, comp,applyTriangle, ← Bool.cond_decide]
      by_cases hyp: (f=t.f ∧ g= t.g)
      · rw [decide_eq_true hyp, cond_true, comp, andThenAssoc,hyp.1,hyp.2, t.trg_com]
      · rw [decide_eq_false hyp, cond_false, comp, ← hr, comp]

theorem diagIsComApplyListT (lt : List (triangle andThen)) (lh : List hom): comp andThen id lh = comp andThen id (applyListTriangles andThen lt lh).2.2 := by
  induction lt with
  | nil =>
    rw [applyListTriangles]
  | cons t q hr =>
    rw [applyListTriangles]
    dsimp
    rw [← Bool.cond_decide]
    by_cases hyp :((applyTriangle andThen t lh).1= true)
    · rw [decide_eq_true hyp, cond_true]
      simp
      --il faut prouver le lien entre le boolen et les modifications ou non dans le programme
      sorry
    · rw [decide_eq_false hyp, cond_false]
      simp
      sorry


theorem diagIsComExpandT (t:triangle andThen) (lh : List hom) (b:Bool): comp andThen id lh = comp andThen id (expandTriangle andThen b t lh).2:= by
  induction lh with
  | nil =>
    rw [expandTriangle]
    congr
    cases b
    repeat rfl
  | cons f q hr =>
    rw [expandTriangle]
    cases b
    · rfl
    · simp
      rw [ ← Bool.cond_decide]
      by_cases hyp: (t.h=f)
      · rw [decide_eq_true hyp, ← hyp, cond_true, comp, comp, comp, andThenAssoc, t.trg_com ]

      · rw [decide_eq_false _, cond_false, comp, comp, hr]
        assumption

theorem diagIsComExpandOneT (lt:List (triangle andThen)) (lh : List hom): comp andThen id lh = comp andThen id (expandOneTriangle andThen lt lh).2.2:= by
  induction lt with
    | nil =>
      rw [expandOneTriangle]
    | cons t q hr =>
      rw [expandOneTriangle]
      let b:= (expandTriangle andThen true t lh).fst
      dsimp
      rw [ ← Bool.cond_decide]
      by_cases hyp : (b=true)
      · rw [decide_eq_true hyp, cond_true, hr]
      · rw [decide_eq_false hyp, cond_false]
        rw [← diagIsComExpandT]
        exact andThenAssoc










theorem diagIsCom (lt: List (triangle andThen)) (lh : List hom): comp andThen id lh = comp andThen id (CommDiag andThen lt lh):= by
  match lh with
    |[] =>
      rw [comp, ]
      sorry
    |f::[] =>
      simp [comp]
      sorry
    |t::q =>
      rw [comp]
      sorry


theorem bidule: if 1=2 then true else false:= by
  refine (Bool.not_ite_eq_false_eq_false (1 = 2) true false).mp ?_

#eval decide (1=2)
