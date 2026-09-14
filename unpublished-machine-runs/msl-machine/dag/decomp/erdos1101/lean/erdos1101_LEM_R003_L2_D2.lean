import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def sylv : Nat → Nat
  | 0 => 2
  | n+1 => sylv n * (sylv n - 1) + 1

theorem msl_erdos1101_lem_r003_l2_c2 (C : ℕ) : ∃ (n : ℕ), sylv n > n ^ C := by sorry
