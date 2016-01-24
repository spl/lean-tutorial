/-------------------------------------------------------------------------------
 -  Section 4.1 The Universal Quantifier
 ------------------------------------------------------------------------------/

variables (A : Type) (p q : A → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  have fwd : (∀ x, p x ∧ q x) → (∀ x, p x) ∧ (∀ x, q x), from
    assume H : ∀ x, p x ∧ q x,
    show (∀ x, p x) ∧ (∀ x, q x), from
    and.intro (take x, and.left (H x)) (take x, and.right (H x)),
  have bwd : (∀ x, p x) ∧ (∀ x, q x) → (∀ x, p x ∧ q x), from
    assume H : (∀ x, p x) ∧ (∀ x, q x),
    show ∀ x, p x ∧ q x, from
    take x,
    and.intro (and.left H x) (and.right H x),
  iff.intro fwd bwd

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  assume (H₁ : ∀ x, p x → q x) (H₂ : ∀ x, p x),
  take x : A,
  show q x, from
  H₁ x (H₂ x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  assume H : (∀ x, p x) ∨ (∀ x, q x),
  take x : A,
  or.elim H
    (assume Hp : ∀ x, p x, or.inl (Hp x))
    (assume Hq : ∀ x, q x, or.inr (Hq x))

variable r : Prop

example : A → ((∀ x : A, r) ↔ r) :=
  assume x : A,
  iff.intro
    (assume f : A → r, f x)
    (assume (r : r) (x : A), r)

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  have fwd : (∀ x, p x ∨ r) → (∀ x, p x) ∨ r, from
    assume H : ∀ x, p x ∨ r,
    -- TODO. This requires classical reasoning.
    sorry,
  have bwd : (∀ x, p x) ∨ r → (∀ x, p x ∨ r), from
    assume H : (∀ x, p x) ∨ r,
    take x : A,
    or.elim H
      (assume Hp : ∀ x, p x, or.inl (Hp x))
      or.inr,
  iff.intro fwd bwd

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  have fwd : (∀ x, r → p x) → (r → ∀ x, p x), from
    assume (H : ∀ x, r → p x) r,
    take x : A,
    H x r,
  have bwd : (r → ∀ x, p x) → (∀ x, r → p x), from
    assume H : r → ∀ x, p x,
    take x : A,
    assume r,
    H r x,
  iff.intro fwd bwd

variables (men : Type) (barber : men) (shaves : men → men → Prop)

example (H : ∀ x : men, shaves barber x ↔ ¬shaves x x) : false :=
  have H' : shaves barber barber ↔ ¬shaves barber barber, from H barber,
  have barber_does_not_shave_himself : ¬shaves barber barber, from
    assume barber_shaves_himself : shaves barber barber,
    iff.elim_left H' barber_shaves_himself barber_shaves_himself,
  barber_does_not_shave_himself (iff.elim_right H' barber_does_not_shave_himself)
