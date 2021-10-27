import data.set

/-
CS2120 F21 HW5

The goals of this assignment are to give you
practice with proofs of propositions that use
existential quantificaton, and to develop your
understanding of formal and informal proofs in
set theory.
-/

/-
PART I: EXISTENTIAL QUANTIFICATION.
-/

/-
To start, suppose that α and β are arbitrary
types, and p and q are predicates on values
of these types: α and β, respectively.
-/

axioms 
  (α β : Type)
  (p : α → Prop)
  (q : β → Prop)

/-
In this context complete the following tasks:

(1) Write a fluent English-language statement
of the proposition to be proved. 

(2) Provide a formal proof of the proposition.

(3) Write an informal proof of the proposition.
-/

-- here's the proposition
example : 
  (∃ (f : α → β), ∀ (a : α), p a → q (f a)) →
  (∃ (a : α), p a) → 
  (∃ (b : β), q b) := 

/-
What does this propositon say? Explain it in
plain English. Here's a start: "If there's a 
function that maps/takes every α value that has
property p to a β value that has property q, then if
there exists an α value with property p, then there exists
a β value with property q.
-/


-- Give your formal proof here
begin
  assume m n,
  cases m,
  cases n,
  apply exists.intro,
  apply m_h n_w,
  exact n_h,
end
  
/-
Assuming that we have two types, α and β and there exists a
function f that produces a β value with property q from an α
value with property p, and that we have an α value a with property p,
we apply f to a to produce a β value with property q, therefore there
exists a β value with property q.
-/