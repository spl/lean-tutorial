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
  sorry

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  sorry
