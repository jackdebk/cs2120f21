-- 1
example : 0 ≠ 1 :=
begin
  -- ¬ (0 = 1)
  -- (0 = 1) → false
  assume h,
  cases h,
end


-- 2
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  have f : false := h (eq.refl 0),
  exact false.elim (f),
end

-- 3
example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  assume (p : P),
  -- ¬¬P
  -- ¬P → false
  -- (P → false) → false
  assume h,
  have f := h p,
  exact f,
end 

-- We might need classical (vs constructive) reasoning 
#check classical.em
open classical
#check em

/-
axiom em : ∀ (p : Prop), p ∨ ¬p

This is the famous and historically controversial
"law" (now axiom) of the excluded middle. It's is
a key to proving many intuitive theorems in logic
and mathematics. But it also leads to giving up on
having evidence *why* something is either true or
not true, in that you no longer need a proof of 
either P or of ¬P to have a proof of P ∨ ¬P.
-/

-- 4
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume h,
  have pornp := classical.em P,
  cases pornp with p pn,
  assumption,
  contradiction,
end

-- 5
theorem demorgan_1 : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  assume P Q,
  apply iff.intro _ _,
    --forward
      assume npq : ¬(P ∧ Q),
        have pnp : P ∨ ¬P := classical.em P,
        have qnq : Q ∨ ¬Q := classical.em Q,
        cases pnp,
          cases qnq,
            have pandq : P ∧ Q,
              exact and.intro pnp qnq,
            contradiction,
            exact or.inr qnq,
          exact or.inl pnp,
    --backward
      assume npnq : ¬P ∨ ¬Q,
      cases npnq,
        assume pandq : P ∧ Q,
        have p : P := and.elim_left pandq,
        contradiction,
        assume pandq : P ∧ Q,
        have q : Q := and.elim_right pandq,
        contradiction,
end


-- 6
theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q) → ¬P ∧ ¬Q :=
begin
  assume P Q,
  assume nporq : ¬ (P ∨ Q),
  apply and.intro _ _,
    assume p : P,
    have porq : P ∨ Q := or.inl p,
    contradiction,
    assume q : Q,
    have porq : P ∨ Q := or.inr q,
    contradiction,
end


-- 7
theorem disappearing_opposite : 
  ∀ (P Q : Prop), P ∨ ¬P ∧ Q ↔ P ∨ Q := 
begin
  assume P Q,
  apply iff.intro _ _,
  --forward
    assume pnpq : P ∨ ¬P ∧ Q,
    cases pnpq,
      exact or.inl pnpq,
      have q : Q := and.elim_right pnpq,
      exact or.inr q,
  --backward
    assume porq : P ∨ Q,
    cases porq,
      exact or.inl porq,
      have pornp : P ∨ ¬P := classical.em P,
      cases pornp,
        exact or.inl pornp,
        have npandq : ¬P ∧ Q := and.intro pornp porq,
        exact or.inr npandq,
end


-- 8
theorem distrib_and_or : 
  ∀ (P Q R: Prop), (P ∨ Q) ∧ (P ∨ R) ↔
                    P ∨ (Q ∧ R) :=
begin
  assume P Q R,
  apply iff.intro _ _,
  --forward
    assume pqpr : (P ∨ Q) ∧ (P ∨ R),
    have porq : P ∨ Q := and.elim_left pqpr,
    have porr : P ∨ R := and.elim_right pqpr,
    cases porq,
      exact or.inl porq,
      cases porr,
        exact or.inl porr,
        have qandr : Q ∧ R := and.intro porq porr,
        exact or.inr qandr,
  --backward
    assume porqr : P ∨ (Q ∧ R),
    apply and.intro _ _,
    cases porqr,
      exact or.inl porqr,
      exact or.inr (and.elim_left porqr),
    cases porqr,
      exact or.inl porqr,
      exact or.inr (and.elim_right porqr),
end

-- remember or is right associative
-- you need this to know what the lefts and rights are
-- 9
theorem distrib_and_or_foil : 
  ∀ (P Q R S : Prop),
  (P ∨ Q) ∧ (R ∨ S) ↔
  (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) :=
begin
  assume P Q R S,
  apply iff.intro _ _,
  --forward
    assume pqrs : (P ∨ Q) ∧ (R ∨ S),
    have porq : P ∨ Q := and.elim_left pqrs,
    have rors : R ∨ S := and.elim_right pqrs,
    cases porq,
      cases rors,
      exact or.inl (and.intro porq rors),
      exact or.inr (or.inl (and.intro porq rors)),
      cases rors,
      exact or.inr (or.inr (or.inl (and.intro porq rors))),
      exact or.inr (or.inr (or.inr (and.intro porq rors))),
  --backward
    assume left : (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S),
    cases left,
      exact and.intro (or.inl (and.elim_left left)) (or.inl (and.elim_right left)),
      cases left,
        exact and.intro (or.inl (and.elim_left left)) (or.inr (and.elim_right left)),
        cases left,
          exact and.intro (or.inr (and.elim_left left)) (or.inl (and.elim_right left)),
          exact and.intro (or.inr (and.elim_left left)) (or.inr (and.elim_right left)),
end


/- 10
Formally state and prove the proposition that
not every natural number is equal to zero.
-/
lemma not_all_nats_are_zero : ∀ (N : ℕ), :=
begin
end 

-- 11. equivalence of P→Q and (¬P∨Q)
example : ∀ (P Q : Prop), (P → Q) ↔ (¬P ∨ Q) :=
begin
  assume P Q,
  apply iff.intro _ _,
  --forward
    assume pthenq : P → Q,
    have pornp : P ∨ ¬P := classical.em P,
    cases pornp,
      exact or.inr (pthenq pornp),
      exact or.inl pornp,
  --backward
    assume nporq : ¬P ∨ Q,
    cases nporq,
      assume p : P,
      contradiction,
      assume P,
      exact nporq,
end

-- 12
example : ∀ (P Q : Prop), (P → Q) → (¬ Q → ¬ P) :=
begin
  assume P Q,
  assume pthenq : P → Q,
  assume nq : ¬Q,
    have pornp : P ∨ ¬P := classical.em P,
    cases pornp,
      have q : Q := pthenq pornp,
      contradiction,
      exact pornp,
end

-- 13
example : ∀ (P Q : Prop), ( ¬P → ¬Q) → (Q → P) :=
begin
  assume P Q,
  assume npthennq : ¬P → ¬Q,
  assume q : Q,
  have pornp : P ∨ ¬P := classical.em P,
  cases pornp,
    exact pornp,
    have nq : ¬Q := npthennq pornp,
    contradiction,
end

