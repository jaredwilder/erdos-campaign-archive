import Mathlib

set_option autoImplicit false


set_option maxHeartbeats 800000

theorem msl_erdos168_monotone_a2 (F : Nat → Rat) h3 : F 3 = 2 h4 : F 4 = 3 h5 : F 5 = 4 h6 : F 6 = 5 : ¬ (F 3 / 3 ≥ F 4 / 4 ∧ F 4 / 4 ≥ F 5 / 5 ∧ F 5 / 5 ≥ F 6 / 6) := by simp only [h3, h4, h5, h6]; decide

-- axiom footprint
#print axioms msl_erdos168_monotone_a2
