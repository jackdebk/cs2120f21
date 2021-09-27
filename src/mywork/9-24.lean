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