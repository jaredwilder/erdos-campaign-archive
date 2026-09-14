import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def sigmaTrial (n : Nat) : Nat :=
  (Finset.filter (fun (d : Nat) => d ∣ n) (Finset.Icc (1 : Nat) n)).sum (fun (d : Nat) => d)

theorem msl_erdos830_demand_r005_l1_1_parent : ∃ (a b : Nat), 1 ≤ a ∧ a ≤ b ∧ sigmaTrial a = a + b ∧ sigmaTrial b = a + b ∧ sigmaTrial a = ∑ d ∈ a.divisors, d ∧ sigmaTrial b = ∑ d ∈ b.divisors, d := by sorry
