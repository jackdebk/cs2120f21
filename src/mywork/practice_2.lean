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
/-
Proof: We assume that P is an arbitrary but specific proposition.
Apply the introduction rule for iff to separate into a forward proof and backwards proof.
Apply the introduction rule for implies assuming a proof of P ∧ P. Apply the left elimination rule for and
on P ∧ P to create a proof of P. To prove it backwards, use the introduction rule for implies to assume a proof of P.
Apply the introduction rule for and using the proof of P twice to create a proof of P ∧ P.
-/

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  --forward
    assume porq: P ∨ Q,
    cases porq,
      exact or.inr porq,
      exact or.inl porq,
  --backward
    assume qorp: Q ∨ P,
    cases qorp,
      exact or.inr qorp,
      exact or.inl qorp,
end
/-Proof: Assume P and Q are propositions. Apply the introduction rule for ↔.
Apply the introduction rule for →. Perform case analysis on P ∨ Q. For the case P ∨ Q : P,
apply the introduction rule for or. For the case P ∨ Q : Q, apply the introduction
rule for or. For the backward proof apply the introduction rule for →. Perform case analysis
on Q ∨ P. For the case Q ∨ P : Q, apply the introduction rule for or. For the case Q ∨ P : P,
apply the introduction rule for or.
-/

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

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
  --forward
    assume pandqorr : P ∧ (Q ∨ R),
    have p : P := and.elim_left pandqorr,
    have qorr : Q ∨ R := and.elim_right pandqorr,
    cases qorr,
      exact or.inl (and.intro p qorr),
      exact or.inr (and.intro p qorr),
  --backward
    assume pqpr : P ∧ Q ∨ P ∧ R,
    cases pqpr,
      have p : P := and.elim_left pqpr,
      exact and.intro p (or.inl (and.elim_right pqpr)),
      have p : P := and.elim_left pqpr,
      exact and.intro p (or.inr (and.elim_right pqpr)),
end
/-Proof: Assume that P, Q, and R are propositions. Apply the introduction rule for ↔.
Apply the introduction rule for → to assume a proof of P ∧ (Q ∨ R). Apply the elimination rule
for and to produce proofs of P and (Q ∧ R). Perform case analysis. Apply the introduction rule
for or and the introduction rule for and for the two cases to prove that for both cases
(P ∧ Q) ∨ (P ∧ R). For the backward proof, apply the introduction rule for →.
Perform case analysis. For the case P ∧ Q, apply the elimination rule for ∧ to create a proof of P.
Apply the introduction rule for ∧ using the proof of P, the introduction rule for ∨ and the elimination rule for ∧.
For the case P ∧ R, apply the elimination rule for ∧ to create a proof of P. Apply the introduction rule for and using
the proof of P, the introduction rule for ∨ and the elimination rule for ∧.
-/

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
    assume pqpr : (P ∨ Q) ∧ (P ∨ R),
    have porq : P ∨ Q := and.elim_left pqpr,
    have porr : P ∨ R := and.elim_right pqpr,
    cases porq,
      exact or.inl porq,
      cases porr,
        exact or.inl porr,
        exact or.inr (and.intro porq porr),
end
/-Proof: Assume that P, Q, and R are arbitrary but specific propositions. Apply the introduction
rule for ↔ to separate into a forward proof and a backwards proof. Use the introduction rule
for → and the left introduction rule for ∨ to create a proof that P → (P ∨ Q).
Use the introduction rule for →, the right introduction rule for ∨, and the left elimination rule
for ∧ to create a proof of (Q ∧ R) → (P ∨ Q). Having shown that P → (P ∨ Q) and (Q ∧ R) → (P ∨ Q),
we can use the elimination rule for ∨ to create a proof of P ∨ Q ∧ R → (P ∨ Q) ∧ (P ∨ R).
To prove the backwards proposition, use the introduction rule for → and the elimination rules for
∧ to separate the proposition into P ∨ Q and P ∨ R. Perform case analysis on P ∨ Q. In the case
where P ∨ Q : P, use the left introduction rule for or. In the case where P ∨ Q : Q,
perform case analysis on P ∨ R. In the case P ∨ R : P, apply the left introduction rule for ∨.
In the case P ∨ R : R, apply the introduction rule for ∧ using Q and R.
-/

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
/-Proof: Assume that P and Q are arbitrary but specific propositions.
Apply the introduction rule for ↔. For the forward proof, apply the introduction rule for
→. Apply the elimination rule for and. For the backward proof, apply the introduction rule for →.
Apply the introduction rule for ∨ to create a proof of P ∧ Q. Apply the introduction rule for and
using the proof of P and the proof of P ∨ Q.
-/
example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  --forward
    assume porpandq: P ∨ (P ∧ Q),
    cases porpandq,
      exact porpandq,
      exact and.elim_left porpandq,
  --backward
    assume p : P,
    exact or.inl p,
end
/-Proof: Assume P is a proposition. Apply the introduction rule for ↔.
For the forward proof, apply the introduction rule for →, assuming a proof P ∨ (P ∧ Q).
Perform case analysis on P ∨ (P ∧ Q). In the first case, we have a proof of P. In the second case,
apply the elimination rule for ∧ on the proof of P ∨ (P ∧ Q). Because both cases prove P, we can use
the elimination rule for ∨. For the backward proof, apply the introduction rule for →, assuming a proof of P.
Apply the introduction rule for ∨ using the proof of P.
-/

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
/-Proof: Assume P is a proposition. Apply the introduction rule for ↔.
For the forward proof, apply the introduction rule for → to assume a proof of P ∨ true.
Apply the introduction rule for true to prove true. For the backward proof, assume a proof of true.
Apply the introduction rule for or using the introduction rule for true to prove P ∨ true.
-/

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  --forward
    assume porf : P ∨ false,
    cases porf,
      exact porf,
      exact false.elim porf,
  --backward
    assume p : P,
    exact or.inl p,
end
/-Proof: Assume that P is an arbitrary but specific proposition. Apply the introduction rule for ↔.
Apply the introduction rule for → to assume P ∨ false. Perform case analysis. In the first case,
we have a proof of P. In the second case, apply the elimination rule for false to show that the case
cannot exist. For the backwards proof, apply the introduction rule for → to assume a proof of P.
Apply the introduction rule for or using the proof of P to prove P ∨ false.
-/

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
/-Proof: Assume that P is an arbitrary but specific proposition. Apply the introduction rule
for ↔. For the forward proof, apply the introduction rule for →. Apply the elimination rule for
∧ to create a proof of P. For the backward proof, apply the introduction rule for →. Apply
the introduction rule for ∧ using the proof of P and the introduction rule for true to create a proof of
P ∨ true.
-/

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro _ _,
  --forward
    assume pandf : P ∧ false,
    have f : false := and.elim_right pandf,
    cases f,
  --backward
    assume f : false,
    apply and.intro _ _,
    exact false.elim f,
    cases f,
end
/-
Proof: Assume that P is an arbitrary but specific proposition. Apply the introduction rule for ↔.
For the forward proof, apply the introduction rule for →. Apply the elimination rule for and to create a proof of false.
Perform case analysis on f, to show that there are no cases where false can be true. For the backwards proof,
apply the introduction rule for → to create a proof f : false. Apply the introduction rule for ∧. Apply the elimination rule for false
to show a contradiction, so we cannot have a proof of P. Perform case analysis on f to show that there are no cases where we have a proof of false.
-/


