import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 4000

open Finset BigOperators

theorem msl_erdos212_lem_r013_l1_c1_triv : ∀ u : Set ℂ, (Dense u ∧ u.Pairwise (fun c₁ c₂ : ℂ => dist c₁ c₂ ∈ Set.range (Rat.cast : Rat → ℝ))) ↔ ∃ v : Set (EuclideanSpace ℝ (Fin 2)), Dense v ∧ v.Pairwise (fun p q : EuclideanSpace ℝ (Fin 2) => dist p q ∈ Set.range (Rat.cast : Rat → ℝ)) := by
  first
  | rfl
  | trivial
  | decide
  | norm_num
  | simp
