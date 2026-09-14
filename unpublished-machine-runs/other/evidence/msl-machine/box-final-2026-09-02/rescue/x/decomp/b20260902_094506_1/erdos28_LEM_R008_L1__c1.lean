import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators
open Filter

def Conv (A : Set ℕ) (n : ℕ) : ℕ :=
  Nat.card {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n}

theorem msl_erdos28_lem_r008_l1_c1 (A : Set ℕ) : (∀ (m : ℕ), ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n → n ∈ A + A) → ∀ (N : ℕ), ∃ (a : ℕ), N ≤ a ∧ a ∈ A := by sorry
