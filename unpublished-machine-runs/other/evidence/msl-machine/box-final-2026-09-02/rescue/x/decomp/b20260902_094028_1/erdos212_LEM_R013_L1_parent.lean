import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

theorem msl_erdos212_lem_r013_l1_parent : answer(sorry) ↔ ∃ u : Set ℂ, Dense u ∧ u.Pairwise (fun c₁ c₂ : ℂ => dist c₁ c₂ ∈ Set.range (Rat.cast : Rat → ℝ)) := by sorry
