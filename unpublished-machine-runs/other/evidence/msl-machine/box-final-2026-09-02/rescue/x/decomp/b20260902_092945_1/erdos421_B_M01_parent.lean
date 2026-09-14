import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def HasDensity (A : Set ℕ) (ρ : Rat) : Prop :=
  Filter.Tendsto (fun (n : ℕ) => (((A ∩ Finset.Icc (1 : ℕ) n).card : ℕ) : Rat) / (n : Rat))
    Filter.atTop (nhds ρ)

theorem msl_erdos421_b_m01_parent (d : ℕ → ℕ) : StrictMono d → ((1 : ℕ) ≤ d 0) → HasDensity (Set.range d) (1 : Rat) →
 ∃ (u v u' v' : ℕ), (u : ℕ) ≤ v ∧ u' ≤ v' ∧ (u, v) ≠ (u', v') ∧
  (∏ i ∈ Finset.Icc u v, d i) = ∏ i ∈ Finset.Icc u' v', d i := by sorry
