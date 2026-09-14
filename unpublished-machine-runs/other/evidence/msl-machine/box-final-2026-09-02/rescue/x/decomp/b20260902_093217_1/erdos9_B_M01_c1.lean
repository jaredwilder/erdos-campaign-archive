import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def erdos9A : Set ℕ :=
  {n : ℕ | Odd n ∧ 1 ≤ n ∧ ∀ (p : ℕ), Nat.Prime p → ∀ (k l : ℕ), p + 2 ^ k + 2 ^ l ≠ n}

theorem msl_erdos9_b_m01_c1 : ∀ (n : ℕ), n ∈ erdos9A ↔
 (Odd n ∧ 1 ≤ n ∧ ∀ (p : ℕ), Nat.Prime p → ∀ (k l : ℕ), p + 2 ^ k + 2 ^ l ≠ n) := by sorry
