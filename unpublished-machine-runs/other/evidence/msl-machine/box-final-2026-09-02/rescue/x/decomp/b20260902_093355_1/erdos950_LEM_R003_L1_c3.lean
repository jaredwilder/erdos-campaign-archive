import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators
open Filter

def erdos950f (n : Nat) : ℝ :=
  ∑ p ∈ Nat.primesBelow n, (1 : ℝ) / ((n : ℝ) - (p : ℝ))

theorem msl_erdos950_lem_r003_l1_c3 : ∀ (N : Nat) (ε : ℝ), 0 < ε → ∃ (n : Nat), N < n ∧ erdos950f n < 1 + ε := by sorry
