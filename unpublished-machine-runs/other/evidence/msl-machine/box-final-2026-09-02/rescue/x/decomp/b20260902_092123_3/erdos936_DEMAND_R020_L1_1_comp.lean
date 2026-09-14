import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

open Finset BigOperators

def Powerful (m : Nat) : Prop := ∀ (p : Nat), p ∣ m → p ^ 2 ∣ m

theorem msl_erdos936_demand_r020_l1_1_composition (k : Nat) : ((3 ∣ (2 ^ (6 * k + 2) + 1)) ∧ (¬ (9 ∣ (2 ^ (6 * k + 2) + 1))) ∧ (∀ (m : Nat), Powerful m → 3 ∣ m → 9 ∣ m)) → (¬ Powerful (2 ^ (6 * k + 2) + 1)) := by
  first
  | tauto
  | (intro h; exact h.1)
  | (intro h; simp_all)
  | (intro h; omega)
  | (intro h; norm_num at h ⊢ <;> tauto)
  | aesop
  | decide

#print axioms msl_erdos936_demand_r020_l1_1_composition
