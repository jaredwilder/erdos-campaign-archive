import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def g2 (n : Nat) : Nat :=
  ((Finset.product (Finset.Icc (0 : Nat) n) (Finset.Icc (0 : Nat) n)).filter
      (fun p : Nat × Nat => p.1.factorial * p.2.factorial ∣ n.factorial)).image
      (fun p : Nat × Nat => p.1 + p.2 - n) |>.sup (fun x : Nat => x)

theorem msl_erdos400_lem_r008_l1_g2_small_range_c1 (n : Nat) : n.factorial * 1.factorial ∣ n.factorial := by sorry
