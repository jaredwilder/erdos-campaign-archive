import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def leastPrimeFactor (m : Nat) : Nat := Nat.minFac m

theorem msl_erdos680_lem_r009_l1_c2 (n : Nat) : (2 : Nat) ≤ n → Even n → leastPrimeFactor (n + (1 : Nat)) > (1 : Nat) ^ (2 : Nat) + (1 : Nat) := by sorry
