import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

open Finset BigOperators

def sylv : Nat → Nat
  | 0 => 2
  | n+1 => sylv n * (sylv n - 1) + 1

theorem msl_erdos1101_lem_r003_l2_composition : ((∀ (n : ℕ), 0 < n → 2 ^ (2 ^ (n - 1)) ≤ sylv n) ∧ (∀ (C : ℕ), ∃ (n : ℕ), sylv n > n ^ C) ∧ (∀ (c : ℝ), 0 < c → ∃ (n : ℕ), (sylv n : ℝ) > Real.exp (c * (n : ℝ)))) → ((∀ (C : ℕ), ∃ (n : ℕ), sylv n > n ^ C) ∧ (∀ (c : ℝ), 0 < c → ∃ (n : ℕ), (sylv n : ℝ) > Real.exp (c * (n : ℝ)))) := by
  first
  | tauto
  | (intro h; exact h.1)
  | (intro h; simp_all)
  | (intro h; omega)
  | (intro h; norm_num at h ⊢ <;> tauto)
  | aesop
  | decide

#print axioms msl_erdos1101_lem_r003_l2_composition
