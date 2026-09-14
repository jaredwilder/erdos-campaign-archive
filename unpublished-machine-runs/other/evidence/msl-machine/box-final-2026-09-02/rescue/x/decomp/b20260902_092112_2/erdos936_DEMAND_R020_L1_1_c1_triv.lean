import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 4000

open Finset BigOperators

def Powerful (m : Nat) : Prop := ∀ (p : Nat), p ∣ m → p ^ 2 ∣ m

theorem msl_erdos936_demand_r020_l1_1_c1_triv (k : Nat) : 3 ∣ (2 ^ (6 * k + 2) + 1) := by
  first
  | rfl
  | trivial
  | decide
  | norm_num
  | simp
