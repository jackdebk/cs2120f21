/-
Conditional Proposition

Axiom = assume the truth of a proposition
-/
namespace implies

axioms (P Q : Prop)

def if_P_is_true_then_so_is_Q : Prop := P → Q
/-
Assume that P is true, then show that Q is true
-/

axiom p : P
-- assume P is true
-- assume we have a proof of P (p)
axiom pq : P → Q
--assume that we have a proof, pq, of P → Q

-- intro for implies: assume premise, show conclusion
-- elimination rule for implies: apply P → Q to p

#check pq
#check p
#check (pq p)

end implies

/-
Suppose P and Q are propositions and you
know that P → Q and P are both true
Show that Q is true.

Proof: Apply the truth of P → Q to the
truth of P to derive the truth of Q.

Proof: By the elimination rule for → with
pq applied to p.

Proof: By "modus ponens". QED
-/

/-
FORALL
-/
namespace all

axioms
  (T : Type)
  (P : T → Prop)
  (t : T)
  (a : ∀ (x : T), P x)

-- Does t have property P?
example: P t := a t

#check a t
end all

/-
AND & →
-/

axioms (P Q : Prop)

/-
Want a proof of P ∧ Q.
-/