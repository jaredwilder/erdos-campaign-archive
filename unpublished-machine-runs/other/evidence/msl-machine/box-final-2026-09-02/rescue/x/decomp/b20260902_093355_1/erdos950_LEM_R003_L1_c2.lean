import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators
open Filter

def erdos950f (n : Nat) : ℝ :=
  ∑ p ∈ Nat.primesBelow n, (1 : ℝ) / ((n : ℝ) - (p : ℝ))

theorem msl_erdos950_lem_r003_l1_c2 : ∀ (ε : ℝ), 0 < ε → ∃ (N : Nat), ∀ (n : Nat), N ≤ n → 1 - ε ≤ erdos950f n := by sorry
