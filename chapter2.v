Require Import BinInt.

Section h_def.
  Variables a b : Z.
  Let s : Z := a + b.
  Let d : Z := a - b.
  Definition h : Z := s * s + d + d.
End h_def.
Print h.
