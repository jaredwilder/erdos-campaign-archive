import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def erdos9A : Set ℕ :=
  {n : ℕ | Odd n ∧ 1 ≤ n ∧ ∀ (p : ℕ), Nat.Prime p → ∀ (k l : ℕ), p + 2 ^ k + 2 ^ l ≠ n}
