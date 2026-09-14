import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

def HasDensity (A : Set ℕ) (ρ : Rat) : Prop :=
  Filter.Tendsto (fun (n : ℕ) => (((A ∩ Finset.Icc (1 : ℕ) n).card : ℕ) : Rat) / (n : Rat))
    Filter.atTop (nhds ρ)

theorem msl_erdos421_b_m01_c3 (N : ℕ) : (Finset.sum (Finset.range N) (fun (i : ℕ) => (i + 1 : ℕ))) = (N : ℕ) * (N + 1) / 2 := by sorry
