import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def erdos9A : Set ℕ :=
  {n : ℕ | Odd n ∧ 1 ≤ n ∧ ∀ (p : ℕ), Nat.Prime p → ∀ (k l : ℕ), p + 2 ^ k + 2 ^ l ≠ n}

theorem msl_erdos9_b_m01_parent : Filter.limsup (fun (N : ℕ) =>
  ((Finset.card (Finset.filter (fun (m : ℕ) => m ∈ erdos9A) (Finset.Icc 1 N) : Finset ℕ) : ℝ)
   / (N : ℝ))) Filter.atTop = 0 := by sorry
