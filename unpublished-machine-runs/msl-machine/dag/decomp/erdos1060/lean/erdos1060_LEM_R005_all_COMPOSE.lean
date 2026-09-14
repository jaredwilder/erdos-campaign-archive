import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000

open Finset BigOperators

def sigma (k : Nat) : Nat := ∑ d ∈ Nat.divisors k, d

def fCount (n : Nat) : Nat :=
  (Finset.filter (fun (k : Nat) => k * sigma k = n) (Finset.Icc 1 n)).card

theorem msl_erdos1060_lem_r005_all_composition : ((∃ (C : ℝ), ∀ (n : Nat), 3 ≤ n → (fCount n : ℝ) ≤ (Real.log (n : ℝ)) ^ C) ∧ (∀ (g : Nat → ℝ), (∃ (C : ℝ), ∀ (n : Nat), 3 ≤ n → g n ≤ (Real.log (n : ℝ)) ^ C) → ∀ (ε : ℝ), ε > 0 → ∃ (N : Nat), ∀ (n : Nat), n ≥ N → g n ≤ (n : ℝ) ^ (ε / Real.log (Real.log n))) ∧ (∀ (n : Nat), fCount n ≤ n)) → (∀ (ε : ℝ), ε > 0 → ∃ (N : Nat), ∀ (n : Nat), n ≥ N → (fCount n : ℝ) ≤ (n : ℝ) ^ (ε / Real.log (Real.log n))) := by
  first
  | tauto
  | (intro h; exact h.1)
  | (intro h; simp_all)
  | (intro h; omega)
  | (intro h; norm_num at h ⊢ <;> tauto)
  | aesop
  | decide

#print axioms msl_erdos1060_lem_r005_all_composition
