import Mathlib

set_option autoImplicit false


set_option maxHeartbeats 1000000

theorem msl_erdos168_monotone_a1 (F : Nat → Nat) (h3 : F 3 = 2) (h4 : F 4 = 3) (h5 : F 5 = 4) (h6 : F 6 = 5) : ¬ ∀ n : Nat, 3 ≤ n → n < 6 → ((F n : Rat) / (n : Rat) ≥ (F (n+1) : Rat) / ((n+1) : Rat)) := by intro h; have h34 := h 3 (by omega) (by omega); rw [h3, h4] at h34; norm_num at h34

-- axiom footprint
#print axioms msl_erdos168_monotone_a1
