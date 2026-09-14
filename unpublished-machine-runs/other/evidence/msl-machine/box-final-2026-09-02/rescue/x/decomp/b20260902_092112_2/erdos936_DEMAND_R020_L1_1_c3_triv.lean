import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 4000

open Finset BigOperators

def Powerful (m : Nat) : Prop := ∀ (p : Nat), p ∣ m → p ^ 2 ∣ m

theorem msl_erdos936_demand_r020_l1_1_c3_triv : ∀ (m : Nat), Powerful m → 3 ∣ m → 9 ∣ m := by
  first
  | rfl
  | trivial
  | decide
  | norm_num
  | simp
