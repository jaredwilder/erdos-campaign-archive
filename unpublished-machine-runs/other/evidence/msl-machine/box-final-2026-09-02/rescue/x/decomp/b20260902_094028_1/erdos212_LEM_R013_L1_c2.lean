import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

theorem msl_erdos212_lem_r013_l1_c2 : ∃ v : Set (EuclideanSpace ℝ (Fin 2)), Dense v ∧ v.Pairwise (fun p q : EuclideanSpace ℝ (Fin 2) => dist p q ∈ Set.range (Rat.cast : Rat → ℝ)) := by sorry
