/-------------------------------------------------------------------------------
 -  Section 3.6 Examples of Propositional Validities
 ------------------------------------------------------------------------------/

variables p q r s : Prop

-- commutativity of ∧ and ∨

lemma and_swap {p q : Prop} (H : p ∧ q) : q ∧ p :=
  and.intro (and.right H) (and.left H)

example : p ∧ q ↔ q ∧ p :=
  iff.intro and_swap and_swap

lemma or_swap {p q : Prop} (H : p ∨ q) : q ∨ p :=
  or.elim H or.inr or.inl

example : p ∨ q ↔ q ∨ p :=
  iff.intro or_swap or_swap

-- associativity of ∧ and ∨

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  iff.intro
    (assume H : (p ∧ q) ∧ r,
      and.intro
        (and.left (and.left H))
        (and.intro (and.right (and.left H)) (and.right H)))
    (assume H : p ∧ (q ∧ r),
      and.intro
        (and.intro (and.left H) (and.left (and.right H)))
        (and.right (and.right H)))

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  iff.intro
    (assume H : (p ∨ q) ∨ r,
      or.elim H
        (assume Hpq, or.elim Hpq or.inl (assume Hq, or.inr (or.inl Hq)))
        (assume Hr, or.inr (or.inr Hr)))
    (assume H : p ∨ (q ∨ r),
      or.elim H
        (assume Hp, or.inl (or.inl Hp))
        (assume Hqr, or.elim Hqr (assume Hq, or.inl (or.inr Hq)) or.inr))

-- distributivity

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  iff.intro
    (assume H : p ∧ (q ∨ r),
      let Hp := and.left H in
      or.elim (and.right H)
        (assume Hq, or.inl (and.intro Hp Hq))
        (assume Hr, or.inr (and.intro Hp Hr)))
    (assume H : (p ∧ q) ∨ (p ∧ r),
      or.elim H
        (assume Hpq, and.intro (and.left Hpq) (or.inl (and.right Hpq)))
        (assume Hpr, and.intro (and.left Hpr) (or.inr (and.right Hpr))))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  iff.intro
    (assume H : p ∨ (q ∧ r),
      or.elim H
        (assume Hp, and.intro (or.inl Hp) (or.inl Hp))
        (assume Hqr, and.intro (or.inr (and.left Hqr)) (or.inr (and.right Hqr))))
    (assume H : (p ∨ q) ∧ (p ∨ r),
      or.elim (and.left H)
        or.inl
        (assume Hq,
          or.elim (and.right H)
            or.inl
            (assume Hr, or.inr (and.intro Hq Hr))))

-- other properties

theorem currying {p q r : Prop} : (p → q → r) ↔ (p ∧ q → r) :=
  iff.intro
    (assume (H : p → q → r) (Hpq : p ∧ q),
      H (and.left Hpq) (and.right Hpq))
    (assume (H : p ∧ q → r) (Hp : p) (Hq : q),
      H (and.intro Hp Hq))

theorem or_power {p q r : Prop} : (p ∨ q → r) ↔ ((p → r) ∧ (q → r)) :=
  have fwd : (p ∨ q → r) → (p → r) ∧ (q → r), from
    assume H, and.intro
      (assume Hp, H (or.inl Hp))
      (assume Hq, H (or.inr Hq)),
  have bwd : (p → r) ∧ (q → r) → (p ∨ q → r), from
    assume H Hpq,
      or.elim Hpq (and.left H) (and.right H),
  iff.intro fwd bwd

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := or_power

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  assume Hnpnq, or.elim Hnpnq
    (assume Hnp : ¬p, not.intro
      (assume Hpq : p ∧ q, not.elim Hnp (and.left Hpq)))
    (assume Hnq : ¬q,
      (assume Hpq : p ∧ q, not.elim Hnq (and.right Hpq)))

example : ¬(p ∧ ¬p) :=
  not.intro (assume H : p ∧ ¬p, and.right H (and.left H))

theorem implication_equiv_fwd {p q : Prop} : (p → q) → ¬(p ∧ ¬q) :=
  assume (H₁ : p → q) (H₂ : p ∧ ¬q),
  and.right H₂ (H₁ (and.left H₂))

theorem implication_equiv_bwd_not {p q : Prop} : p ∧ ¬q → ¬(p → q) :=
  assume H₁ : p ∧ ¬q,
  not.intro (assume H₂ : p → q, implication_equiv_fwd H₂ H₁)

example : ¬p → (p → q) :=
  assume (Hnp : ¬p) (Hp : p),
  absurd Hp Hnp

theorem implication_equiv_bwd {p q : Prop} : ¬p ∨ q → (p → q) :=
  assume (H : ¬p ∨ q) (Hp : p),
  or.elim H (absurd Hp) id

example : (¬p ∨ q) → (p → q) := implication_equiv_bwd

example : p ∨ false ↔ p :=
  have fwd : p ∨ false → p, from
    assume H, or.elim H id false.elim,
  have bwd : p → p ∨ false, from
    assume Hp, or.inl Hp,
  iff.intro fwd bwd

example : p ∧ false ↔ false :=
  have fwd : p ∧ false → false, from
    and.right,
  have bwd : false → p ∧ false, from
    assume H, and.intro (false.elim H) H,
  iff.intro fwd bwd

-- From https://github.com/leanprover/tutorial/issues/157
example : ¬(p ↔ ¬p) :=
  assume H : p ↔ ¬p,
  have Hnp : ¬p, from
    assume Hp : p,
    iff.elim_left H Hp Hp,
  Hnp (iff.elim_right H Hnp) 

example : (p → q) → (¬q → ¬p) :=
  assume Hpq Hnq,
  show ¬p, from
  assume Hp, Hnq (Hpq Hp)

-- these require classical reasoning

open classical

-- This is a classical proof (using em) of one of the above examples.
example : ¬(p ↔ ¬p) :=
  assume H : p ↔ ¬p,
  have Hfwd : p → ¬p, from iff.elim_left H,
  have Hbwd : ¬p → p, from iff.elim_right H,
  or.elim (em p)
    (assume Hp, Hfwd Hp Hp)
    (assume Hnp, Hfwd (Hbwd Hnp) (Hbwd Hnp))

theorem implication_classical_equiv_fwd {p q : Prop} : (p → q) → (¬p ∨ q) :=
  assume Hpq : p → q,
  or.elim (em p)
    (assume Hp : p, or.inr (Hpq Hp))
    (assume Hnp : ¬p, or.inl Hnp)

theorem implication_classical_equiv_bwd {p q : Prop} : ¬(p ∧ ¬q) → (p → q) :=
  assume (H : ¬(p ∧ ¬q)) (Hp : p),
  show q, from
    or.elim (em q) id (assume Hnq, absurd (and.intro Hp Hnq) H)

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
  assume H : p → r ∨ s,
  or.elim (implication_classical_equiv_fwd H)
    (assume Hnp : ¬p, or.inl (assume Hp : p, absurd Hp Hnp))
    (assume Hrs : r ∨ s,
      or.elim Hrs
        (assume Hr : r, or.inl (assume Hp : p, Hr))
        (assume Hs : s, or.inr (assume Hp : p, Hs)))

theorem not_and_distribution {p q : Prop} : ¬(p ∧ q) → ¬p ∨ ¬q :=
  assume H : ¬(p ∧ q),
  implication_classical_equiv_fwd (assume Hp Hq,
    not.elim H (and.intro Hp Hq))

example : ¬(p → q) → p ∧ ¬q :=
  assume H : ¬(p → q),
  or.elim (em p)
    (assume Hp, or.elim (em q)
      (assume Hq, and.intro
        Hp
        (assume Hq, H (assume Hp, Hq)))
      (assume Hnq, and.intro Hp Hnq))
    (assume Hnp, or.elim (em q)
      (assume Hq, and.intro
        (by_contradiction (assume Hnp, H (assume Hp, Hq)))
        (not.intro (assume Hq, H (assume Hp, Hq))))
      (assume Hnq, and.intro
        (by_contradiction (assume Hnp, H (assume Hp, absurd Hp Hnp)))
        Hnq))

example : (p → q) → (¬p ∨ q) := implication_classical_equiv_fwd

example : (¬q → ¬p) → (p → q) :=
  assume (H : ¬q → ¬p) (Hp : p),
  or.elim (em q) id (assume Hnq, absurd Hp (H Hnq))

example : p ∨ ¬p := em p

example : ((p → q) → p) → p :=
  assume H : (p → q) → p,
  or.elim (em p) id (assume Hnp,
    or.elim (em q)
      (assume Hq, H (assume Hp, Hq))
      (assume Hnq, H (assume Hp, absurd Hp Hnp)))
