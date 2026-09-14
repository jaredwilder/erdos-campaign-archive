import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 4000

open Finset BigOperators

def erdos306R003L : Finset ℕ := {6, 10, 14, 15, 21, 22}

theorem msl_erdos306_lem_r003_l1_c5_triv : ∀ d ∈ erdos306R003L, ((∃ x ∈ erdos306R003L, ∃ y ∈ erdos306R003L, x ≠ y ∧ (1:ℚ)/(d) = (1:ℚ)/(x) + (1:ℚ)/(y)) ↔ d = 6) := by
  first
  | rfl
  | trivial
  | decide
  | norm_num
  | simp
