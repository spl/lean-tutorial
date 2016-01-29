open bool option

definition option.comp {A B C : Type} (f : A → option B) (g : B → option C) (x : A) : option C :=
  option.cases_on (f x) none
    (λ y : B, option.cases_on (g y) none some)

example : inhabited bool := inhabited.mk tt

example : inhabited ℕ := inhabited.mk 0

example {A B : Type} (x : inhabited A) (y : inhabited B) : inhabited (A × B) :=
  inhabited.cases_on x (λ a : A,
  inhabited.cases_on y (λ b : B,
  inhabited.mk (a, b)))

example {A B : Type} (f : A → inhabited B) : inhabited (A → inhabited B) := inhabited.mk f
