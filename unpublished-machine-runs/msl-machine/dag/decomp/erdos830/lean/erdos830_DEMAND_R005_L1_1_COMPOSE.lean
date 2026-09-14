import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

open Finset BigOperators

def sigmaTrial (n : Nat) : Nat :=
  (Finset.filter (fun (d : Nat) => d ∣ n) (Finset.Icc (1 : Nat) n)).sum (fun (d : Nat) => d)

theorem msl_erdos830_demand_r005_l1_1_composition : ((∀ (n : Nat), n ≤ (300 : Nat) → sigmaTrial n = ∑ d ∈ n.divisors, d)) → (∃ (a b : Nat), 1 ≤ a ∧ a ≤ b ∧ sigmaTrial a = a + b ∧ sigmaTrial b = a + b ∧ sigmaTrial a = ∑ d ∈ a.divisors, d ∧ sigmaTrial b = ∑ d ∈ b.divisors, d) := by
  first
  | tauto
  | (intro h; exact h.1)
  | (intro h; simp_all)
  | (intro h; omega)
  | (intro h; norm_num at h ⊢ <;> tauto)
  | aesop
  | decide

#print axioms msl_erdos830_demand_r005_l1_1_composition
