/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro
/- Prove True
Using the introduction rule for true, which is that
true is axiomatically true.
-/

example : false := _   -- trick question? why?
/- We cannot prove false because by definition, false has no proof
-/

example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  --forward
    assume p_or_p: P ∨ P,
    apply or.elim p_or_p,
    assume p : P,
    exact p,
    assume p : P,
    exact p,
  --backward
    assume p,
    apply or.intro_left _ _,
    exact p,
end
/-
Prove that P or P is true if and only if we have a proof of P.
We must prove that if P or P is true, then P is true,
and that if P is true, then P or P is true. First, assume that
we have a proof of P or P. Apply the elimination rule for or 
on P or P. Then if we have a proof of the first argument of the or,
P, then we have a proof of P. If we have a proof of the second argument,
P, then we have a proof of P, so we have a proof that if P or P,
then P is true. Then we must prove that if P is true, then P or P
is true. We assume that we have a proof of P. We then use this proof
of P in the left introduction rule for or on P or P, which gives a
proof of P or P.
-/

example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  --forward
    assume p_and_p : P ∧ P,
    apply and.elim_left p_and_p,
  --backward
    assume P,
    apply and.intro _ _,
    exact P,
    exact P,
end


--work on this
example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  --forward
    assume p_or_q: P ∨ Q,
    have pthenqorp : P → Q ∨ P,
      assume p : P,
      exact or.inr p,
    have qthenqorp : Q → Q ∨ P,
      assume q : Q,
      exact or.inl q,
    exact or.elim p_or_q pthenqorp qthenqorp,
  --backward
    assume q_or_p: Q ∨ P,
    have qthenporq : Q → P ∨ Q,
      assume q : Q,
      exact or.inr q,
    have pthenporq : P → P ∨ Q,
      assume p : P,
      exact or.inl p,
    exact or.elim q_or_p qthenporq pthenporq,
end

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  --forward
    assume p_and_q: P ∧ Q,
    apply and.intro _ _,
    exact and.elim_right p_and_q,
    exact and.elim_left p_and_q,
  --backward
    assume q_and_p: Q ∧ P,
    apply and.intro _ _,
    exact and.elim_right q_and_p,
    exact and.elim_left q_and_p,
end
/-
Prove that P and Q is true if and only if Q and P is true.
Assume that Q and P are arbitrary but specific propositions.
First, prove the forward direction, that Q and P is true
if P and Q is true. Assume that we have a proof of Q and P.
Then, apply the left elimination rule for and on the proof of P and Q
to get a proof of P. Apply the right elimination rule for and on the proof of P and Q to get
a proof of Q. Apply the introduction rule for and using the proof
of P and proof of Q to create a proof of Q and P. Then, prove the
reverse direction, that P and Q is true if Q and P is true.
Assume that we have a proof of Q and P. Apply the left elimination
rule for and on the proof of Q and P to get a proof of Q. 
Apply the right elimination rule for and on the proof of Q and P
to get a proof of P. Apply the introduction rule for and using 
the proof of P and proof of Q to create a proof of P and Q.

-/

--Work on
example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
  --forward
    assume pandqorr : P ∧ (Q ∨ R),
    have p : P := and.elim_left pandqorr,
    have qorr : Q ∨ R := and.elim_right pandqorr,
    have qorrthenpqpr : Q ∨ R → (P ∧ Q) ∨ (P ∧ R),
      assume qorr,
      have qthenpqpr : Q → (P ∧ Q) ∨ (P ∧ R),
        assume q : Q,
        exact or.inl (and.intro p q),
      have rthenpqpr : R → (P ∧ Q) ∨ (P ∧ R),
        assume r : R,
        exact or.inr (and.intro p r),
      exact or.elim qorr qthenpqpr rthenpqpr,
  --backward
end

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
  --forward
    assume porqandr : P ∨ (Q ∧ R),
    apply and.intro _ _,
    have pthenpq : P → (P ∨ Q),
      assume p : P,
      exact or.inl p,
    have qrthenpq: (Q ∧ R) → (P ∨ Q),
      assume qandr : Q ∧ R,
      exact or.inr (and.elim_left qandr),
    exact or.elim porqandr pthenpq qrthenpq,
    have pthenpr : P → (P ∨ R),
      assume p : P,
      exact or.inl p,
    have qrthenpr: (Q ∧ R) → (P ∨ R),
      assume qandr : Q ∧ R,
      exact or.inr (and.elim_right qandr),
    exact or.elim porqandr pthenpr qrthenpr,
  --backward
end

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  --forward
    assume pandporq : P ∧ (P ∨ Q),
    have p : P := and.elim_left pandporq,
    exact p,
  --backward
    assume p : P,
    have porq : P ∨ Q := or.inl p,
    apply and.intro p porq,
end

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  --forward
    assume porpandq: P ∨ (P ∧ Q),
    have pp : P → P,
    assume P,
    exact P,
    have pandqthenp : (P ∧ Q) → P,
    assume pandq : P ∧ Q,
    have p := and.elim_left pandq,
    exact p,
    show P,
    from or.elim porpandq pp pandqthenp,
  --backward
    assume p : P,
    apply or.inl _,
    exact p,
end

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P,
  apply iff.intro _ _,
  --forward
    assume port : P ∨ true,
    exact true.intro,
  --backward
    assume t : true,
    exact or.intro_right P true.intro,
end

--work on this
example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  --forward
    assume porf : P ∨ false,
    have notfalsethenp : ¬ false → P
    
  --backward
end

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  --forward
    assume pandt : P ∧ true,
    apply and.elim_left pandt,
  --backward
    assume p : P,
    apply and.intro _ _,
    exact p,
    exact true.intro,
end


--work on this
example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro _ _,
  --forward
    assume pandf : P ∧ false,
    have f : false := and.elim_right pandf,
    exact f,
  --backward
    assume f : false,
    apply and.intro _ _,
end


