import Mathlib

set_option autoImplicit false
set_option maxRecDepth 4000

open Finset BigOperators

noncomputable def IntervalSum (p : ℕ+ × ℕ+) : ℚ := ∑ x ∈ Set.Icc p.1 p.2, ((x : ℚ)⁻¹)

def Good (I : Fin 2 → ℕ+ × ℕ+) : Prop :=
  ∀ j, (I j).1 ≤ (I j).2 ∧ ∃ n : ℕ+, ∑ j : Fin 2, IntervalSum (I j) = (n : ℚ)

theorem msl_erdos288_lem_r003_certification_c2 (I : Fin 2 → ℕ+ × ℕ+) : 0 < ∑ j : Fin 2, IntervalSum (I j) := by sorry
