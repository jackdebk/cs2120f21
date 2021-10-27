import data.set
/-
Jack de Bruyn Kops
HAE3RA
HW 6
-/
/-
Exercise: Prove that for any set, L, L ∩ L = L.
-/
example : 
  ∀ {α : Type} (L : set α), L ∩ L = L :=
  begin
    assume a h,
    apply set.ext _,
      assume x,
      apply iff.intro,
      --forward
        assume xinh,
        cases xinh with m1 m2,
          exact m1,
      --backward
        assume xinh,
        apply and.intro xinh xinh,
  end

/-
Exercise: Give a formal statement and proof, then an 
English language proof, that the union operator on 
sets is commutative.
-/
example :
  ∀ {α : Type} (A B : set α), A ∪ B = B ∪ A :=
  begin
    assume α a b,
    apply set.ext _,
      assume x,
      apply iff.intro,
      --forward
        assume aub,
        cases aub,
          exact or.inr aub,
          exact or.inl aub,
      --backward
        assume bua,
        cases bua,
          exact or.inr bua,
          exact or.inl bua,
  end

/-
Proof:
Assume that we have an arbitrary type α and two sets of type α,
a and b. To prove that A ∪ B = B ∪ A, we must prove that for any arbitrary
value x of type α, if it is in the union of a and b then it must be in
the union of b and a, and vice versa. In the forward direction, we assume that
x is in the union of a and b. Therefore, by case analysis, either x is in a
or x is in b. If x is in a, then it is in the union of b and a, and if x is in b,
then it is in the union of b and a. The the reverse direction, we assume
that x is in the union of b and a. Therefore, by case analysis, either x is in b
or x is in a. If x is in b, then it is in the union of a and b, and if x is in a,
then it is in the union of a and b.
-/
/-
Exercise: Prove that ⊆ is reflexive and transitive.
Give a formal statement, a formal proof, and an English
language (informal) proof of this fact.
-/
example :
  ∀ {α : Type} (a: set α), (a ⊆ a) :=
  begin
    assume α a,
    assume v,
    assume vina,
    exact vina,   
  end

/-
Proof:
Assume that we have an arbitrary type, α, and an arbitrary
set of type α, a. Assume an arbitrary α value v, and that v is a member
of a. Therefore, v is a member of a, so every value v that is a member of
a is a member of a, and a is a subset of a.
-/
example :
  ∀ {α : Type} (a b c : set α), (a ⊆ b → b ⊆ c → a ⊆ c) :=
  begin
    assume α,
    assume a b c,
    assume asubb bsubc,
    assume v,
    assume vina,
    have vinb : v ∈ b := asubb vina,
    exact bsubc vinb,
  end

/-
Proof:
Assume that we have an arbitrary type α and three arbitrary sets of
type α, a, b, and c. Assume that a is a subset of b and b is a subset of c.
Assume an arbitrary αlpha value v and that v is in a. v is in b because
a is a subset of b, therefore because v is in b, v is in c because b
is a subset of c. Therefore for all α values, if they are in a, they are in c,
so a is a subset of c.
-/
/-
Exercise: Prove that ∪ and ∩ are associative.
Give a formal statement, a formal proof, and an 
English language (informal) proof of this fact.
-/
example :
  ∀ {α : Type} (a b c : set α), (a ∪ (b ∪ c)) = ((a ∪ b) ∪ c) :=
  begin
    assume α a b c,
    apply set.ext,
    assume x,
    apply iff.intro,
    --forward
      assume xinabc,
      cases xinabc,
      exact or.inl (or.inl xinabc),
      cases xinabc with b c,
        exact or.inl (or.inr b),
        exact or.inr c,
    --backward
      assume xinabc,
      cases xinabc,
      cases xinabc with a b,
      exact or.inl a,
      exact or.inr (or.inl b),
      exact or.inr (or.inr xinabc),
  end
/-
Proof:
Assume an arbitrary type α and three sets of type α, a, b, and c. 
To prove that (a ∪ (b ∪ c)) = ((a ∪ b) ∪ c), we must prove that for any α
value x, if x is a member of a ∪ (b ∪ c), then x is a member of (a ∪ b) ∪ c
and vice versa. In the forward direction, assume that x is a member of a ∪ (b ∪ c).
By case analysis, either x is in a or x is in the union of b and c. If x
is in a, it is in the union of a and b, therefore x is in (a ∪ b) ∪ c. If x is in
the union of b and c, either x is in b or x is in c. If x is in b, it is in
the union of a and b, therefore x is in (a ∪ b) ∪ c. If x is in c, then therefore it
is in (a ∪ b) ∪ c. In the backward direction, assume that x is a member of (a ∪ b) ∪ c).
By case analysis, either x is in the union of a and b or x is in c. If x
is in the union of a and b, then either x is in a or x is in b. If x is in a, then
it is in a ∪ (b ∪ c). If x is in b, then it is in the union of b and c, so it is
in a ∪ (b ∪ c). If x is in c, then x is in the union of b and c, therefore x is in
a ∪ (b ∪ c).
-/

example :
  ∀ {α : Type} (a b c : set α), ((a ∩ (b ∩ c)) = ((a ∩ b) ∩ c)) :=
  begin
    assume α a b c,
    apply set.ext,
    assume x,
    apply iff.intro,
    --forward
      assume xinabc,
      have xina : x ∈ a := and.elim_left xinabc,
      have xinb : x ∈ b := and.elim_left (and.elim_right xinabc),
      have xinc : x ∈ c := and.elim_right (and.elim_right xinabc),
      apply and.intro _ xinc,
      exact and.intro xina xinb,
    -- backward
      assume xinabc,
      have xina : x ∈ a := and.elim_left (and.elim_left xinabc),
      have xinb : x ∈ b := and.elim_right (and.elim_left xinabc),
      have xinc : x ∈ c := and.elim_right xinabc,
      apply and.intro xina,
      exact and.intro xinb xinc,
  end
/-
Proof:
Assume an arbitrary type α and three sets of type α, a, b, and c. To prove
that (a ∩ (b ∩ c)) = ((a ∩ b) ∩ c), we must prove that for any α value x,
if x is a member of (a ∩ (b ∩ c), then it is a member of (a ∩ b) ∩ c), and vice versa.
In the forward direction, assume that x is in a ∩ (b ∩ c). x must be a member of
both a and the intersection of b and c. Therefore, x must be in both b and c.
x must be a member of the intersection of a and b because x is a member of both a and b,
therefore x must be a member of (a ∩ b) ∩ c because x is in the intersection of
a and b and is in c. In the reverse direction, assume that x is in (a ∩ b) ∩ c.
x must be in c and in the intersection of a and b, so x must be in both a and b.
Because x is in both b and c, x is in b ∩ c, so because x is in b ∩ c and a,
x is a member of a ∩ (b ∩ c).
-/
/-
Assignment: read (at least skim) the Sections 1 and 2 of 
the Wikipedia page on set identities: 
https://en.wikipedia.org/wiki/List_of_set_identities_and_relations 
There, , among *many* other facts, you will find definitions 
of left and right distributivity. To complete the remainder
of this assignment, you need to understand what it means for 
one operator to be left- (or right-) distributive over another. 
-/


/-
Exercise: Formally state and prove both formally and 
informally that ∩ is left-distributive over ∩.
-/
example :
  ∀ {α : Type} (a b c: set α), (a ∩ (b ∩ c)) = ((a ∩ b) ∩ (a ∩ c)) :=
  begin
    assume α a b c,
    apply set.ext,
    assume x,
    apply iff.intro,
    --forward
    assume xinabc,
    have xina : x ∈ a := and.elim_left xinabc,
    have xinb : x ∈ b := and.elim_left (and.elim_right xinabc),
    have xinc : x ∈ c := and.elim_right (and.elim_right xinabc),
    apply and.intro,
    apply and.intro xina xinb,
    apply and.intro xina xinc,
    --backward
    assume xinabac,
    have xina : x ∈ a := and.elim_left (and.elim_left xinabac),
    have xinb : x ∈ b := and.elim_right (and.elim_left xinabac),
    have xinc : x ∈ c := and.elim_right (and.elim_right xinabac),
    apply and.intro xina,
    exact and.intro xinb xinc,
  end
/-
Proof:
Assume an arbitrary type α and three sets of type α, a b c. To prove that
(a ∩ (b ∩ c)) = ((a ∩ b) ∩ (a ∩ c)), we must show that for any α value x,
if x is a member of (a ∩ (b ∩ c)), then x is a member of ((a ∩ b) ∩ (a ∩ c)).
In the forward direction, assume that x is a member of a ∩ (b ∩ c). x must
be in a and in b ∩ c, so x must be in both b anc c. Because x is in both a and b,
x is in a ∩ b, and because x is in both a and c, x is in a ∩ c. x is in both a ∩ b
and a ∩ c, so x is in (a ∩ b) ∩ (a ∩ c). In the reverse direction, we assume that
x is in (a ∩ b) ∩ (a ∩ c). x must be in both a ∩ b and a ∩ c, therefore x is in both
a and b and a and c. x must be in b ∩ c because x is in b and c, so x is in a ∩ (b ∩ c)
because x is in a and in b ∩ c.
-/
/-
Exercise: Formally state and prove both formally 
and informally that ∪ is left-distributive over ∩.
-/
example :
  ∀ {α : Type} (a b c : set α), a ∪ (b ∩ c) = (a ∪ b) ∩ (a ∪ c) :=
  begin
    assume α a b c,
    apply set.ext,
    assume x,
    apply iff.intro,
    --forward
      assume xinabc,
      cases xinabc with a bc,
      apply and.intro,
      exact or.inl a,
      exact or.inl a,
      apply and.intro,
        exact or.inr (and.elim_left bc),
        exact or.inr (and.elim_right bc),
    --backward
      assume xinabac,
      have aorb : x ∈ a ∪ b := and.elim_left xinabac,
      have aorc : x ∈ a ∪ c := and.elim_right xinabac,
      cases aorb with a b,
        exact or.inl a,
        cases aorc with a c,
        exact or.inl a,
        exact or.inr (and.intro b c),
  end
/-
Proof:
Assume an arbitrary type α and three sets of type alpha, a b c.
To prove that a ∪ (b ∩ c) = (a ∪ b) ∩ (a ∪ c), we must show that for any
α value x, if x is in a ∪ (b ∩ c), then x is in (a ∪ b) ∩ (a ∪ c) and vice versa.
In the forward direction, assume that x is in a ∪ (b ∩ c). Either x is in a or x is in b ∩ c.
If x is in a, then x is in a ∪ b and x is in a ∪ c, therefore x is in (a ∪ b) ∩ (a ∪ c).
If x is in b ∩ c, then x is in both b and c. Therefore, x is in (a ∪ b) and
x is in (a ∪ c). Therefore, x is in (a ∪ b) ∩ (a ∪ c). In the reverse direction, we assume
that x is in (a ∪ b) ∩ (a ∪ c). x must be in both a ∪ b and a ∪ c. x is in either a or b,
If x is in a, then x is in a ∪ (b ∩ c). If x is in b, then perform case analysis on x is in
a ∪ c. If x is in a, then x is in a ∪ (b ∩ c). If x is in c, then x is in both b and c, so x
is in b ∩ c, so x is in a ∪ (b ∩ c).
-/

