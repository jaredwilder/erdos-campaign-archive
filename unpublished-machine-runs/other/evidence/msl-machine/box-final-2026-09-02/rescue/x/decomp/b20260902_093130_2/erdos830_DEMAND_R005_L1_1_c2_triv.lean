import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 4000

open Finset BigOperators

def sigmaTrial (n : Nat) : Nat :=
  (Finset.filter (fun (d : Nat) => d ∣ n) (Finset.Icc (1 : Nat) n)).sum (fun (d : Nat) => d)

theorem msl_erdos830_demand_r005_l1_1_c2_triv : ∀ (n : Nat), n ≤ (300 : Nat) → sigmaTrial n = ∑ d ∈ n.divisors, d := by
  first
  | rfl
  | trivial
  | decide
  | norm_num
  | simp
