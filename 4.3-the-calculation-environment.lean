import data.nat
open nat algebra

example (x y : ℕ) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc  (x + y) * (x + y)
      = (x + y) * x + (x + y) * y         : left_distrib
  ... = x * x + y * x + (x + y) * y       : right_distrib
  ... = x * x + y * x + (x * y + y * y)   : right_distrib
  ... = x * x + y * x + x * y + y * y     : add.assoc

example (x y : ℕ) : (x - y) * (x + y) = x * x - y * y :=
  calc  (x - y) * (x + y)
      = x * (x + y) - y * (x + y)          : nat.mul_sub_right_distrib
  ... = x * (x + y) - (y * x + y * y)      : left_distrib
  ... = (x * x + x * y) - (y * x + y * y)  : left_distrib
  ... = (x * x + y * x) - (y * x + y * y)  : mul.comm
  ... = (y * x + x * x) - (y * x + y * y)  : add.comm
  ... = x * x - y * y                      : nat.add_sub_add_left
