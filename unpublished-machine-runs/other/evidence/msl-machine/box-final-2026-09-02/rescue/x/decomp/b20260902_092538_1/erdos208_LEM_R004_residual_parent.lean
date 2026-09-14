import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def s : ℕ → ℕ := fun n => Nat.nth (fun k => Squarefree k) n

def gap (n : ℕ) : ℕ := s (n + 1) - s n

theorem msl_erdos208_lem_r004_residual_parent : (∀ (ε : ℝ), 0 < ε → ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n → ((gap n : ℝ) ≤ (s n : ℝ) ^ ε)) ∧ (∀ (ε : ℝ), 0 < ε → ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n → ((gap n : ℝ) ≤ (1 + ε) * (π ^ 2 / 6) * Real.log (s n : ℝ) / Real.log (Real.log (s n : ℝ)))) := by sorry
