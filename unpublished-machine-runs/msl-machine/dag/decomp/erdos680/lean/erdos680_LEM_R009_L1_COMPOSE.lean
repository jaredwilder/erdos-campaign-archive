import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

open Finset BigOperators

def leastPrimeFactor (m : Nat) : Nat := Nat.minFac m

theorem msl_erdos680_lem_r009_l1_composition : ((∀ (n : Nat) (k : Nat), Nat.Prime (n + k) → n + k > k ^ (2 : Nat) + (1 : Nat) → leastPrimeFactor (n + k) > k ^ (2 : Nat) + (1 : Nat)) ∧ (∀ (n : Nat), (2 : Nat) ≤ n → Even n → leastPrimeFactor (n + (1 : Nat)) > (1 : Nat) ^ (2 : Nat) + (1 : Nat)) ∧ (∀ (n : Nat), (2 : Nat) ≤ n → Odd n → ¬((3 : Nat) ∣ n + (2 : Nat)) → ¬((5 : Nat) ∣ n + (2 : Nat)) → leastPrimeFactor (n + (2 : Nat)) > (2 : Nat) ^ (2 : Nat) + (1 : Nat)) ∧ (∃ (N : Nat), ∀ (n : Nat), N ≤ n → Odd n → (((3 : Nat) ∣ n + (2 : Nat)) ∨ ((5 : Nat) ∣ n + (2 : Nat))) → ∃ (k : Nat), (0 : Nat) < k ∧ Nat.Prime (n + k) ∧ n + k > k ^ (2 : Nat) + (1 : Nat))) → (∃ (N : Nat), ∀ (n : Nat), N ≤ n → ∃ (k : Nat), (0 : Nat) < k ∧ leastPrimeFactor (n + k) > k ^ (2 : Nat) + (1 : Nat)) := by
  first
  | tauto
  | (intro h; exact h.1)
  | (intro h; simp_all)
  | (intro h; omega)
  | (intro h; norm_num at h ⊢ <;> tauto)
  | aesop
  | decide

#print axioms msl_erdos680_lem_r009_l1_composition
