import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def HasDensity (A : Set ℕ) (ρ : Rat) : Prop :=
  Filter.Tendsto (fun (n : ℕ) => (((A ∩ Finset.Icc (1 : ℕ) n).card : ℕ) : Rat) / (n : Rat))
    Filter.atTop (nhds ρ)

theorem msl_erdos421_b_m01_c5 (d : ℕ → ℕ) (ε : Rat) : ((0 : Rat) < ε) → ε < 1 → StrictMono d → ((1 : ℕ) ≤ d 0) → HasDensity (Set.range d) (1 : Rat) →
 ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n →
  (((Set.range d ∩ Finset.Icc (1 : ℕ) n).card : ℕ) : Rat) > ((1 : Rat) - ε) * (n : Rat) := by sorry
