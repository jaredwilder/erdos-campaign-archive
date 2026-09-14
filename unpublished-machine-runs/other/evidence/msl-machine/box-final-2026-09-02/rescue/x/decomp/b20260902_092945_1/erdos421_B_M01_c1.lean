import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def HasDensity (A : Set ℕ) (ρ : Rat) : Prop :=
  Filter.Tendsto (fun (n : ℕ) => (((A ∩ Finset.Icc (1 : ℕ) n).card : ℕ) : Rat) / (n : Rat))
    Filter.atTop (nhds ρ)

theorem msl_erdos421_b_m01_c1 (g : ℕ × ℕ → ℕ) (S : Finset (ℕ × ℕ)) (B : ℕ) : (S.card : ℕ) > B → (∀ (p : ℕ × ℕ), p ∈ S → g p ≤ B) →
 ∃ (p : ℕ × ℕ), ∃ (q : ℕ × ℕ), p ∈ S ∧ q ∈ S ∧ p ≠ q ∧ g p = g q := by sorry
