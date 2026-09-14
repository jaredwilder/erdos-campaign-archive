import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def leastPrimeFactor (m : Nat) : Nat := Nat.minFac m

theorem msl_erdos680_lem_r009_l1_c1 (n : Nat) (k : Nat) : Nat.Prime (n + k) → n + k > k ^ (2 : Nat) + (1 : Nat) → leastPrimeFactor (n + k) > k ^ (2 : Nat) + (1 : Nat) := by sorry
