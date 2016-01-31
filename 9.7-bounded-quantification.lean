import data.nat
open nat decidable algebra

definition bex (n : nat) (P : nat → Prop) : Prop :=
∃ x : nat, x < n ∧ P x

definition not_bex_zero (P : nat → Prop) : ¬ bex 0 P :=
sorry

variables {n : nat} {P : nat → Prop}

definition bex_succ (H : bex n P) : bex (succ n) P :=
sorry

definition bex_succ_of_pred  (H : P n) : bex (succ n) P :=
sorry

definition not_bex_succ (H₁ : ¬ bex n P) (H₂ : ¬ P n) : ¬ bex (succ n) P :=
sorry

definition dec_bex [instance] (H : decidable_pred P) : Π (n : nat), decidable (bex n P) :=
sorry
