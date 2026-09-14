import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 4000

open Finset BigOperators

def erdos9A : Set ℕ :=
  {n : ℕ | Odd n ∧ 1 ≤ n ∧ ∀ (p : ℕ), Nat.Prime p → ∀ (k l : ℕ), p + 2 ^ k + 2 ^ l ≠ n}

theorem msl_erdos9_b_m01_c1_triv : ∀ (n : ℕ), n ∈ erdos9A ↔
 (Odd n ∧ 1 ≤ n ∧ ∀ (p : ℕ), Nat.Prime p → ∀ (k l : ℕ), p + 2 ^ k + 2 ^ l ≠ n) := by
  first
  | rfl
  | trivial
  | decide
  | norm_num
  | simp
