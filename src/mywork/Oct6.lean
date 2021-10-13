/-

-/

axioms
  (Person : Type)
  (Likes : Person → Person → Prop)

example :
  ¬ (∀ p : Person, Likes p p) ↔
  ∃ p : Person, ¬ Likes p p :=
begin
  apply iff.intro _ _,
  --forward
    assume h,
    have f := classical.em (∃ p : Person, ¬ Likes p p),
    cases f,
      exact f,
      have contra : ∀ (p : Person), Likes p p := _,
      contradiction,
      assume p : Person,
      have g := classical.em (Likes p p),
      cases g,
        exact g,
        have expnlp : ∃ (p : Person), ¬ Likes p p,
        apply exists.intro p g,
        contradiction,
  --backward
    assume h,
    assume n : ∀ (p : Person), Likes p p,
end