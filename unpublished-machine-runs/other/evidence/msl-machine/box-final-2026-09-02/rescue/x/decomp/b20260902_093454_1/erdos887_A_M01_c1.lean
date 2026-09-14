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

theorem msl_erdos887_a_m01_c1 (n : ℕ) (C₁ C₂ : ℝ) : 0 < C₁ → C₁ ≤ C₂ → countWindow n C₁ ≤ countWindow n C₂ := by sorry
