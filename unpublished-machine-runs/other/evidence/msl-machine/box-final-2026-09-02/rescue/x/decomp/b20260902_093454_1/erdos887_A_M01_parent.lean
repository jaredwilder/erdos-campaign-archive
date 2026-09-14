import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def windowDivisors (n : ℕ) (C : ℝ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun (d : ℕ) =>
    ((n : ℝ) ^ ((1 : ℝ) / 2) < (d : ℝ)) ∧
    ((d : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 2) + C * (n : ℝ) ^ ((1 : ℝ) / 4)) ∧
    (d ∣ n)

def countWindow (n : ℕ) (C : ℝ) : ℕ := (windowDivisors n C).card

theorem msl_erdos887_a_m01_parent : ∃ (K : ℕ), ∀ (C : ℝ), 0 < C → ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → countWindow n C ≤ K := by sorry
