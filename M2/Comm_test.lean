import Mathlib.Tactic
import Mathlib.Data.Nat.Defs
import Lean

open Lean Meta Elab Tactic

variable (hom:Type) [DecidableEq hom] [ToString hom]--(andThen: hom → hom → hom) --[Std.Associative  andThen]

--(andThenAssoc: ∀ f g h, andThen f (andThen g h)= andThen (andThen f g) h)

--variable {obj:Type} (dom codom: hom → obj)

@[ext]
structure triangle where--f≫ g=h
  f : hom
  g : hom
  h : hom
  --trg_com: andThen f g = h
deriving Repr

-- le booléen est à true si on n'a rien changé et false si on à modifié un truc
def applyTriangle (t : triangle hom) (c : List hom ): MetaM (Bool × List hom) := match c with
  |[] => return (true, c)
  |_ :: [] => return (true, c)
  |a :: b :: cprime => do
    if a = t.f ∧ b = t.g then
      logInfo m!"the composition {t.f} ≫ {t.g} is replaced by {t.h}"
      return (false, t.h :: cprime)
    else
      let (b,newc) ←  applyTriangle t (b::cprime)
      return (b, a::newc)

-- le booléen est à true si on n'a rien changé et false si on à modifié un truc
def applyListTriangles (lt : List (triangle hom)) (c : List hom ) : MetaM (Bool × List (triangle hom) × List hom) :=
  match lt with
    |[] => return (true, [], c)
    |t::ltprime => do
      let (b, newc) ←  applyTriangle hom t c
      let (newbool, newlt, newc) ←  applyListTriangles ltprime newc
      if b then return (true, t::newlt, newc)
      else return (newbool, newlt, newc)

/-theorem applyListTrianglesDec (lt:List (triangle hom)): ∀ (lh:List hom ), sizeOf (applyListTriangles hom lt lh ).2.1 ≤ sizeOf lt  := by
  induction lt with
  | nil =>
    intro
    apply Nat.le_refl
  | cons t q hr =>
    intro lh
    rw [applyListTriangles]
    suffices sizeOf (if (applyTriangle hom t lh).1 = true then
          (true, t :: (applyListTriangles hom q (applyTriangle hom t lh).2).2.1,
            (applyListTriangles hom q (applyTriangle hom t lh).2).2.2)
        else applyListTriangles hom q (applyTriangle hom t lh).2).2.1 ≤
  1 + sizeOf t + sizeOf q by simpa
    split_ifs
    · rw [List.cons.sizeOf_spec, Nat.add_le_add_iff_left]
      apply hr
    · linarith [hr ( applyTriangle hom t lh).2]

theorem applyListTrianglesDecLength (lt:List (triangle hom)): ∀ (lh:List hom ), List.length (applyListTriangles hom lt lh ).2.1 ≤ List.length lt  := by
  induction lt with
  | nil =>
    intro
    apply Nat.le_refl
  | cons t q hr =>
    intro lh
    rw [applyListTriangles]
    suffices List.length (if (applyTriangle hom t lh).1 = true then
          (true, t :: (applyListTriangles hom q (applyTriangle hom t lh).2).2.1,
            (applyListTriangles hom q (applyTriangle hom t lh).2).2.2)
        else applyListTriangles hom q (applyTriangle hom t lh).2).2.1 ≤
  List.length q + 1by simpa
    split_ifs
    · exact Nat.le_add_of_sub_le (hr (applyTriangle hom t lh).2)
    · linarith [hr ( applyTriangle hom t lh).2]-/


-- le booléen est à true si on n'a rien changé et false si on à modifié un truc
def expandTriangle (ok : Bool) (t : triangle hom) (c : List hom ) : MetaM (Bool × List hom ):=
  if not ok then return (false, c)
  else  match c with
    |[] => return (ok,c)
    |a :: cprime => do
      if  (t.h = a) then
      logInfo m!"the morphism {t.h} is replaced by the composition {t.f} ≫ {t.g}"
      return (false, t.f :: t.g :: cprime)
      else
        let (newok, newc) ←  expandTriangle  ok t cprime
        return (newok, a::newc)

-- le booléen est à true si on n'a rien changé et false si on à modifié un truc
def expandOneTriangle (lt : List (triangle hom)) (c : List hom ) : MetaM (Bool × List (triangle hom)× List hom) := match lt with
  |[]=> return (true, lt, c)
  |t :: ltprime => do
    let (b, newc) ←  expandTriangle hom true t c
    if b then
      let (newbool, ltprimeprime, newnewc) ←  expandOneTriangle ltprime c
      return (newbool, t::ltprimeprime, newnewc)
    else
      return (false, ltprime,newc)

/-theorem expandOneTriangleDec (lt:List (triangle hom)) (c:List hom ): (expandOneTriangle hom lt c ).1 = false → sizeOf (expandOneTriangle hom lt c ).2.1 < sizeOf lt  := by
  induction lt with
  | nil =>
    intro hyp
    rw [expandOneTriangle] at hyp
    exfalso
    exact (Bool.eq_not_self (true, [], c).fst).mp hyp
  |cons t q hr =>
    intro hyp
    rw [expandOneTriangle]
    suffices sizeOf (if _ then _ else (false, q, (expandTriangle hom true t c).2)).2.1 < 1 + sizeOf t + sizeOf q by simpa

    split_ifs with hypp
    · rw [ List.cons.sizeOf_spec]
      have : (expandOneTriangle hom q c).fst = false := by
        rw [expandOneTriangle] at hyp
        simp only at hyp
        split_ifs at hyp
        exact hyp
      linarith [hr this]
    · linarith-/

 partial def CommDiag (lt:List (triangle hom)) (lh : List hom ): MetaM (List hom) := do
  let alt ←  applyListTriangles hom lt lh
  let eot ←  expandOneTriangle hom alt.2.1 alt.2.2

  if hyp : not eot.1 then
    CommDiag eot.2.1 eot.2.2
  else return alt.2.2
/-termination_by lt
decreasing_by
  calc sizeOf eot.2.1 < sizeOf alt.2.1  := by {
        apply expandOneTriangleDec
        apply Bool.not_inj_iff.mp
        rw [hyp]
        simp}
        _ ≤ sizeOf lt  := by apply applyListTrianglesDec-/

variable (a b c: Nat)

def t: triangle Nat where
  f := a
  g := b
  h := c
  --trg_com := sorry


#eval! t 1 2 3

def lt : List (triangle Nat):= (t 1 3 2) :: (t 3 4 5) :: List.nil

def l : List Nat := 1 :: 5 :: List.nil

#eval! lt

#eval! applyListTriangles Nat lt [1,3,4]

#eval! expandOneTriangle Nat lt l

#eval! CommDiag Nat lt l

/-
variable (id: hom)

def comp (c: List hom): hom := match c with
  |[] => id --on aimerait s'en passer mais ça introduit une disjonction de cas penible dans la preuve de composition qui suit
  |t::q => andThen t (comp q)
def IsStableByComp (f:List hom → List hom):Prop:= ∀ (lh: List hom), comp andThen id lh = comp andThen id (f lh)

theorem ISBCComp (f g: List hom → List hom) (hf: IsStableByComp andThen id f) (hg : IsStableByComp andThen id g):IsStableByComp andThen id (fun l => g (f l)):= by
  intro lh
  rw [hf, hg]


variable {idNeutral: ∀ f, andThen f id = f}

lemma applyTrianglesSpec (t:triangle andThen) (c:List hom ):  (applyTriangle andThen t c).1 → (applyTriangle andThen t c).2 = c  := by
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
      split_ifs with hypp
      · rw [applyTriangle] at hyp
        split_ifs at hyp
      · rw [applyTriangle] at hyp
        split_ifs at hyp
        suffices (applyTriangle andThen t (g :: qq)).2 = g :: qq by simpa
        exact hr hyp

/-lemma expandOneTriangleToNil (lt: List (triangle andThen)): expandOneTriangle andThen lt [] = (true, lt, []) := by
  induction lt with
  | nil => rfl
  | cons t q hr =>
    rw [expandOneTriangle, expandTriangle, ← Bool.cond_decide, decide_eq_false, cond_false]
    · suffices (expandOneTriangle andThen q []).1 = true ∧(expandOneTriangle andThen q []).2.1 = q ∧ (expandOneTriangle andThen q []).2.2 = [] by simpa
      rw [hr]
      exact ⟨ rfl, rfl, rfl⟩
    · rw [Bool.not_true, Bool.false_eq_true, not_false_eq_true]
      trivial

lemma applyListTrianglesToNil (lt: List (triangle andThen)): applyListTriangles andThen lt [] = (true, lt, []) := by
  induction lt with
  | nil => rfl
  | cons t q hr =>
    rw [applyListTriangles, applyTriangle]
    suffices (applyListTriangles andThen q []).2.1 = q ∧ (applyListTriangles andThen q []).2.2 = [] by simpa
    constructor
    · rw [hr]
    · rw [hr]-/

variable [Std.Associative andThen]

lemma andThenAssoc: ∀ f g h, andThen f (andThen g h)= andThen (andThen f g) h := by
  intro _ _ _
  rw [← @Std.Associative.assoc _ andThen]


lemma diagIsComApplyT (t : triangle andThen): IsStableByComp andThen id (fun lh => (applyTriangle andThen t lh).2):= by
  intro lh
  induction lh with
  | nil => rfl
  |cons f q hr =>
    match q with
    | [] => rfl
    | g :: qq  =>
      beta_reduce
      rw [comp, comp, applyTriangle]
      split_ifs with hyp
      · rw [ comp, andThenAssoc andThen, hyp.1, hyp.2, t.trg_com]
      · rw [ comp, ← hr, comp]

theorem diagIsComApplyListT (lt : List (triangle andThen)): IsStableByComp andThen id ( fun lh => (applyListTriangles andThen lt lh).2.2 ):= by
  induction lt with
  | nil =>
    intro _
    rfl
  | cons t q hr =>
    intro lh
    beta_reduce
    rw [applyListTriangles]

    suffices comp andThen id lh = comp andThen id (if _ then (true, t :: (applyListTriangles andThen q (applyTriangle andThen t lh).2).2.1, (applyListTriangles andThen q (applyTriangle andThen t lh).2).2.2)-- on doit pouvoir simplifier ça mais wip
        else _ ).2.2 by simpa

    split_ifs with hyp
    · rw [hr, applyTrianglesSpec _ _ _ hyp]
    · apply ISBCComp _ _ _ _ _ hr
      apply diagIsComApplyT andThen id t

theorem diagIsComExpandT (t:triangle andThen) (b:Bool): IsStableByComp andThen id (fun lh => (expandTriangle andThen b t lh).2) := by
  intro lh
  induction lh with
  | nil =>
    beta_reduce
    rw [expandTriangle]
    congr
    cases b
    repeat rfl
  | cons f q hr =>
    beta_reduce
    rw [expandTriangle]
    cases b
    · rfl
    · suffices comp andThen id (f :: q) = comp andThen id (if t.h = f then (false, t.f :: t.g :: q)
      else ((expandTriangle andThen true t q).1, f :: (expandTriangle andThen true t q).2)).2 by simpa
      split_ifs with hyp
      · rw [← hyp, comp, comp, comp, andThenAssoc andThen, t.trg_com ]
      · rw [ comp, comp, hr]


theorem diagIsComExpandOneT (lt:List (triangle andThen)): IsStableByComp andThen id (fun lh => (expandOneTriangle andThen lt lh).2.2) := by
  induction lt with
    | nil =>
      intro _
      rfl
    | cons t q hr =>
      intro lh
      beta_reduce
      rw [expandOneTriangle]
      suffices comp andThen id lh = comp andThen id (if (expandTriangle andThen true t lh).1 = true then
          ((expandOneTriangle andThen q lh).1, t :: (expandOneTriangle andThen q lh).2.1,
            (expandOneTriangle andThen q lh).2.2)
        else (false, q, (expandTriangle andThen true t lh).2)).2.2 by simpa

      split_ifs with hyp
      · rw [ hr]
      · rw [← diagIsComExpandT]



-- pourquoi ça ne marche pas sans
def propAux: Nat → Prop := fun n => ∀  (lt: List (triangle andThen)) (lh : List hom), (hlt : List.length lt = n) →  comp andThen id lh = comp andThen id (CommDiag andThen lt lh)

theorem diagIsComN (k: Nat): propAux andThen id k:= by
  apply Nat.strongRecOn
  intro n hn lt lh hlt
  match n with
    | 0 =>
      have : lt = []:= by
        apply List.length_eq_zero.mp
        linarith
      rw [this, CommDiag]
      suffices _ = comp andThen id (if _ then _ else _ ) by simpa

      split_ifs with hyp
      · rw [ applyListTriangles, expandOneTriangle] at hyp
        cases hyp
      · rfl
    | n + 1 =>
      rcases List.exists_cons_of_length_eq_add_one hlt with ⟨t,q,tconsqeqlt⟩
      rw [tconsqeqlt, CommDiag]

      split_ifs with hyp
      · rw [← hn _ _]
        · rw [← diagIsComExpandOneT andThen ,diagIsComApplyListT andThen]
        · rfl
        · calc List.length _ < List.length _  := by {
            apply expandOneTriangleDecLength andThen
            apply Bool.not_inj_iff.mp
            rw [hyp]
            simp}
            _ ≤ (t :: q).length  := by apply applyListTrianglesDecLength
            _ = n + 1 := by rw [ ← tconsqeqlt, hlt]
      · rw [ ← diagIsComApplyListT]


theorem diagIsCom (lt : List (triangle andThen)) : IsStableByComp andThen id (fun lh => CommDiag andThen lt lh) := by
  intro _
  apply diagIsComN
  rfl
-/
