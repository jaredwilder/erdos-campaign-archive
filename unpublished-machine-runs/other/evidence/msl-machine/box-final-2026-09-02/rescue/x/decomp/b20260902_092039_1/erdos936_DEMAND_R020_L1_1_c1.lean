import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def Powerful (m : Nat) : Prop := ∀ (p : Nat), p ∣ m → p ^ 2 ∣ m

theorem msl_erdos936_demand_r020_l1_1_c1 (k : Nat) : 3 ∣ (2 ^ (6 * k + 2) + 1) := by sorry
