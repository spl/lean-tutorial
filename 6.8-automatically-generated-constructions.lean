inductive tree (A : Type) : Type :=
| leaf : A → tree A
| node : tree A → tree A → tree A

open tree

variable {A : Type}

theorem leaf_ne_node {a : A} {l r : tree A}
  (h : leaf a = node l r) : false :=
    tree.no_confusion h

theorem leaf_inj {a b : A} (h : leaf a = leaf b) : a = b :=
  tree.no_confusion h id

theorem node_inj_left {l1 r1 l2 r2 : tree A}
  (h : node l1 r1 = node l2 r2) : l1 = l2 :=
    tree.no_confusion h (λ e₁ e₂, e₁)

theorem node_inj_right {l1 r1 l2 r2 : tree A}
  (h : node l1 r1 = node l2 r2) : r1 = r2 :=
    tree.no_confusion h (λ e₁ e₂, e₂)
