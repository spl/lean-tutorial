open classical

variables (A : Type) (p : A → Prop)

example (H : ¬∀ x, ¬p x) : ∃ x, p x :=
  by_contradiction
    (assume Hnep : ¬∃ x, p x,
    have Hanp : ∀ x, ¬p x, from
      take x : A,
      assume Hpx : p x,
      have Hep : ∃ x, p x, from
        exists.intro x Hpx,
      show false, from Hnep Hep,
    show false, from H Hanp)

variables (a : A) (r : Prop)

example : (∃ x : A, r) → r :=
  assume H : ∃ x : A, r,
  obtain (w : A) (Hr : r), from H,
  show r, from Hr

example : r → (∃ x : A, r) :=
  assume Hr : r,
  show ∃ x : A, r, from
    exists.intro a Hr

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  have fwd : (∃ x, p x ∧ r) → (∃ x, p x) ∧ r, from
    assume H : ∃ x, p x ∧ r,
    obtain (w : A) (H' : p w ∧ r), from H,
    show (∃ (x : A), p x) ∧ r, from and.intro
      (exists.intro w (and.left H'))
      (and.right H'),
  have bwd : (∃ x, p x) ∧ r → (∃ x, p x ∧ r), from sorry,
  iff.intro fwd bwd

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  have fwd : (∃ x, p x ∨ q x) → (∃ x, p x) ∨ (∃ x, q x), from
    assume H : ∃ x, p x ∨ q x,
    obtain (w : A) (Hw : p w ∨ q w), from H,
    or.elim Hw
      (assume Hpw : p w, or.inl (exists.intro w Hpw))
      (assume Hqw : q w, or.inr (exists.intro w Hqw)),
  have bwd : (∃ x, p x) ∨ (∃ x, q x) → (∃ x, p x ∨ q x), from
    assume H : (∃ x, p x) ∨ (∃ x, q x),
    or.elim H
      (assume Hp : ∃ x, p x, obtain (w : A) (Hw : p w), from Hp, exists.intro w (or.inl Hw))
      (assume Hq : ∃ x, q x, obtain (w : A) (Hw : q w), from Hq, exists.intro w (or.inr Hw)),
  iff.intro fwd bwd

-- This requires classical for the bwd case.
example : (∀ x, p x) ↔ ¬(∃ x, ¬p x) :=
  have fwd : (∀ x, p x) → ¬(∃ x, ¬p x), from
    assume (Ha : ∀ x, p x) (He : ∃ x, ¬p x),
    obtain (w : A) (Hw : ¬p w), from He,
    show false, from Hw (Ha w),
  have bwd : ¬(∃ x, ¬p x) → (∀ x, p x), from
    assume H : ¬(∃ x, ¬p x),
    take (x : A),
    by_contradiction (assume Hnp : ¬p x, H (exists.intro x Hnp)),
  iff.intro fwd bwd

example : (∃ x, p x) ↔ ¬(∀ x, ¬p x) :=
  have fwd : (∃ x, p x) → ¬(∀ x, ¬p x), from
    assume (He : ∃ x, p x) (Ha : ∀ x, ¬p x),
    obtain (w : A) (Hw : p w), from He,
    show false, from Ha w Hw,
  have bwd : ¬(∀ x, ¬p x) → (∃ x, p x), from
    assume H : ¬(∀ x, ¬p x),
    have Ha : ∀ x, ¬p x, from sorry,
    exists.intro sorry sorry,
  iff.intro fwd bwd

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
example : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
example : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
