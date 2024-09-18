import Mathlib.tactics

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

theorem applyListTrianglesDec (lt:List (triangle andThen)): ∀ (lh:List hom ), sizeOf (applyListTriangles andThen lt lh ).2.1 ≤ sizeOf lt  := by
  induction lt with
  | nil =>
    intro
    apply Nat.le_refl
  | cons t q hr =>
    intro lh
    rw [applyListTriangles]
    simp
    by_cases hyp: (applyTriangle andThen t lh).fst = true
    · rw [← Bool.cond_decide, decide_eq_true hyp, cond_true, List.cons.sizeOf_spec, Nat.add_le_add_iff_left]
      apply hr
    · rw [← Bool.cond_decide, decide_eq_false hyp, cond_false,]
      simp
      --linarith [hr lh]
      sorry


-- le booléen est à true si on n'a rien changé et false si on à modifié un truc
def expandTriangle (ok:Bool) (t:triangle andThen) (c:List hom ): Bool × List hom :=
  if not ok then (false,c)
  else  match c with
    |[] => (ok,c)
    |a :: cprime =>
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

theorem expandOneTriangleDec (lt:List (triangle andThen)) (c:List hom ): (expandOneTriangle andThen lt c ).1 = false → sizeOf (expandOneTriangle andThen lt c ).2.1 < sizeOf lt  := by
  induction lt with
  | nil =>
    intro hyp
    rw [expandOneTriangle] at hyp
    exfalso
    exact (Bool.eq_not_self (true, [], c).fst).mp hyp
  |cons t q hr =>
    intro hyp
    rw [expandOneTriangle]
    simp
    by_cases hypp: ((expandTriangle andThen true t c).fst = true )
    · rw [← Bool.cond_decide, decide_eq_true hypp, cond_true, List.cons.sizeOf_spec]
      have : (expandOneTriangle andThen q c).fst = false := by
        rw [expandOneTriangle] at hyp
        simp only at hyp
        rw [← Bool.cond_decide, decide_eq_true hypp, cond_true ] at hyp
        exact hyp
      --linarith [hr this]
      sorry


    · rw [← Bool.cond_decide, decide_eq_false hypp, cond_false]
      simp
      --linarith
      sorry


/--def IsValid (l:List hom): Prop:= match l with
  |[]=> True
  |_ :: [] => True
  |f :: g :: lprime => (codom f = dom g) ∧ (IsValid (g :: lprime))--/

 def CommDiag (lt:List (triangle andThen)) (lh : List hom ): List hom :=
  let (_, newlt, newl) := applyListTriangles andThen lt lh
  let (b, newnewlt, newnewl) := expandOneTriangle andThen newlt newl

  if not b then
    have : sizeOf newnewlt <  sizeOf lt := by
      calc sizeOf newnewlt < sizeOf newlt  := by {

        sorry
      }
        _ ≤ sizeOf lt  := by {

          --exact applyListTrianglesDec andThen lt lh
          sorry}


    CommDiag newnewlt newnewl
  else newl

variable (a b c: Nat)

def t: triangle Nat.add where
  f := a
  g := b
  h := c
  trg_com := sorry


#eval! t 1 2 3

def lt : List (triangle Nat.add):= (t 1 3 2) :: (t 3 4 5) :: List.nil

def l : List Nat := 1 :: 5 :: List.nil

#eval! lt

#eval! applyListTriangles Nat.add lt [1,3,4]

#eval! expandOneTriangle Nat.add lt l

#eval! CommDiag Nat.add lt l

variable (id: hom)

def comp (c: List hom): hom := match c with
  |[] => id --on aimerait s'en passer mais ça introduit une disjonction de cas penible dans la preuve de composition qui suit
  |t::q => andThen t (comp q)


variable (andThenAssoc: ∀ f g h, andThen f (andThen g h)= andThen (andThen f g) h)

variable {idNeutral: ∀ f, andThen f id = f}

def IsStableByComp (f:List hom → List hom):Prop:= ∀ (lh: List hom), comp andThen id lh = comp andThen id (f lh)

theorem ISBCComp (f g: List hom → List hom) (hf: IsStableByComp andThen id f) (hg : IsStableByComp andThen id g):IsStableByComp andThen id (fun l => g (f l)):= by
  intro lh
  rw [hf, hg]

theorem applyTrianglesSpec (t:triangle andThen) (c:List hom ):  (applyTriangle andThen t c).1 → (applyTriangle andThen t c).2 = c  := by
  induction c with
  | nil =>
    intro _
    rw [applyTriangle]
  | cons f q hr => match q with
    | [] =>
      intro _
      rw [applyTriangle]
    | g :: qq =>
      intro hyp
      rw [applyTriangle]
      by_cases hypp: (f = t.f ∧ g = t.g)
      · rw [applyTriangle, ← Bool.cond_decide, decide_eq_true hypp, cond_true] at hyp
        exfalso
        apply (Bool.eq_not_self (false, t.h :: qq).fst).mp hyp
      · rw [ ← Bool.cond_decide, decide_eq_false hypp, cond_false]
        rw [applyTriangle, ← Bool.cond_decide, decide_eq_false hypp, cond_false] at hyp
        simp only [List.cons.injEq, true_and]
        exact hr hyp

theorem expandOneTriangleToNil (lt: List (triangle andThen)): expandOneTriangle andThen lt [] = (true, lt, []) := by
  induction lt with
  | nil => rfl
  | cons t q hr =>
    rw [expandOneTriangle, expandTriangle, ← Bool.cond_decide, decide_eq_false, cond_false]
    simp
    rw [hr]
    exact ⟨ by rfl, by rfl, by rfl⟩

    rw [Bool.not_true, Bool.false_eq_true, not_false_eq_true]
    trivial

theorem applyListTrianglesToNil (lt: List (triangle andThen)): applyListTriangles andThen lt [] = (true, lt, []) := by
  induction lt with
  | nil => rfl
  | cons t q hr =>
    rw [applyListTriangles, applyTriangle]
    simp
    constructor
    · rw [hr]
    · rw [hr]

theorem diagIsComApplyT (t : triangle andThen): IsStableByComp andThen id (fun lh => (applyTriangle andThen t lh).2):= by
  intro lh
  induction lh with
  | nil => rfl
  |cons f q hr =>
    match q with
    | [] => rfl
    | g :: qq  =>
      simp -- c'est une beta réduction, on devrait pouvoir faire sans mais betaReduce n'existe pas ici
      rw [comp, comp, applyTriangle, ← Bool.cond_decide]
      by_cases hyp: (f = t.f ∧ g = t.g)
      · rw [decide_eq_true hyp, cond_true, comp, andThenAssoc, hyp.1, hyp.2, t.trg_com]
      · rw [decide_eq_false hyp, cond_false, comp, ← hr, comp]


theorem diagIsComApplyListT (lt : List (triangle andThen)): IsStableByComp andThen id ( fun lh => (applyListTriangles andThen lt lh).2.2 ):= by
  induction lt with
  | nil =>
    intro _
    rfl
  | cons t q hr =>
    intro lh
    simp --toujours cette histoire de beta reduction
    rw [applyListTriangles]
    dsimp
    rw [← Bool.cond_decide]
    by_cases hyp :((applyTriangle andThen t lh).1= true)
    · rw [decide_eq_true hyp, cond_true, hr, applyTrianglesSpec _ _ _ hyp]
    · rw [decide_eq_false hyp, cond_false]

      apply ISBCComp _ _ _ _ _ hr
      apply diagIsComApplyT andThen id t



theorem diagIsComExpandT (t:triangle andThen) (b:Bool): IsStableByComp andThen id (fun lh => (expandTriangle andThen b t lh).2) := by
  intro lh
  induction lh with
  | nil =>
    simp --la beta redudction
    rw [expandTriangle]
    congr
    cases b
    repeat rfl
  | cons f q hr =>
    simp --la beta reduction
    rw [expandTriangle]
    cases b
    · rfl
    · simp
      rw [ ← Bool.cond_decide]
      by_cases hyp: (t.h=f)
      · rw [decide_eq_true hyp, ← hyp, cond_true, comp, comp, comp, andThenAssoc, t.trg_com ]

      · rw [decide_eq_false _, cond_false, comp, comp, hr]
        assumption

theorem diagIsComExpandOneT (lt:List (triangle andThen)): IsStableByComp andThen id (fun lh => (expandOneTriangle andThen lt lh).2.2) := by
  induction lt with
    | nil =>
      intro _
      rfl
    | cons t q hr =>
      intro lh
      simp
      rw [expandOneTriangle]
      dsimp
      rw [ ← Bool.cond_decide]
      by_cases hyp : ( (expandTriangle andThen true t lh).fst = true)
      · rw [decide_eq_true hyp, cond_true, hr]
      · rw [decide_eq_false hyp, cond_false]
        rw [← diagIsComExpandT]


theorem diagIsComN (n: Nat): ∀  (lt: List (triangle andThen)) (lh : List hom), (hlt : List.length lt ≤ n) →  comp andThen id lh = comp andThen id (CommDiag andThen lt lh):= by
  apply Nat.case_strong_induction_on

  /-induction n with
    | zero =>
      intro lt lh hlt
      have : lt = []:= by
        apply List.length_eq_zero.mp
        --linarith
        sorry
      rw [this, CommDiag]
      dsimp
      rw [ ← Bool.cond_decide, decide_eq_false, cond_false, applyListTriangles]
      rw [applyListTriangles, expandOneTriangle]
      exact Bool.not_not_eq.mpr rfl
    | succ n hr =>
      intro lt lh lth
      match lth with
        |


      sorry


  /--
    | nil =>
      rw [comp, CommDiag, ]

      simp
      rw [ ← Bool.cond_decide, decide_eq_false, cond_false, applyListTrianglesToNil, comp]
-- les deux en un seul bloc ça ne passe pas
      rw [applyListTrianglesToNil, expandOneTriangleToNil, Bool.true_eq_false, not_false_eq_true]
      trivial
    | cons f q hr =>
      rw [ CommDiag,]
      dsimp
      rw [ ← Bool.cond_decide]
      by_cases hyp: (expandOneTriangle andThen (applyListTriangles andThen lt (f :: q)).2.fst (applyListTriangles andThen lt (f :: q)).2.snd).fst = true
      · rw [decide_eq_false , cond_false, ← diagIsComApplyListT, comp]
        intro hypp
        rw [hyp, Bool.not_true, Bool.false_eq_true] at hypp
        exact hypp

      · rw [decide_eq_true, cond_true]

        dsimp
        sorry
