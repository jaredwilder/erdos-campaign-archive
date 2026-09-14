import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators
open Filter

def Conv (A : Set ℕ) (n : ℕ) : ℕ :=
  Nat.card {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n}

theorem msl_erdos28_lem_r008_l1_c4 (A : Set ℕ) : (∀ (m : ℕ), ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n → n ∈ A + A) →
 ∀ (M : ℕ) (N : ℕ), ∃ (n : ℕ), N ≤ n ∧ M ≤ Conv A n := by sorry
