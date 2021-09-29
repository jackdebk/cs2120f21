/-Intro rules
=
  1
∧
  1
∨
  2
∀
  assume
→
  assume
¬
  P→False
↔
  1
∃
true
  1
false
  0

Elim Rules
=
  1
∧
  2
∨
  1
∀
  apply
→
  apply
¬
↔
∃
true
  0
false
  false.elim
-/

example : 0 ≠ 1 :=
begin
  assume p : 0 = 1,
  cases p,
end

example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  have f : false := h (eq.refl 0),
  exact false.elim (f),
end

example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  assume p : P,
  assume h,
  contradiction,
end

#check classical.em
open classical
#check em

/-
em : ∀ (p : Prop), p ∨ ¬p
-/
/-*******
Negation elimination
Allows you to eliminate double eliminations.
-/
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume nnp,
  have pornp := em P,
  cases pornp,
    exact pornp,
    contradiction,
end

/-
9-27
Existentially quantified
Introduction rule
Pair: Witness to the proposition, proof that that number is even

Predicate
(ev: ℕ → Prop)
ev 7
ev 8
-/

--def ev (n : nat):Prop:= n%2=0,

--def le (n m : ℕ): Prop :=
--begin
  
--end
/-
le : 2 place predicate
le 3 : 1 place predicate
le 3 6 : 0 place predicate, aka proposition
-/

def pt (m n p : ℕ) : Prop := (m*m + n*n = p*p)

example: ∃ (a b c : ℕ), pt a b c :=
begin
  apply exists.intro 3,
  apply exists.intro 4,
  apply exists.intro 5,
  unfold pt,
  apply eq.refl,
end

--elimination rule for exists, if we have an existance, give it a name.

