import Mathlib

set_option autoImplicit false



-- no auxiliary definitions

theorem msl_fmz_erdos400_campaign_001_R002_L1_a2r4  : ([] : List Nat) = [] ∧ ¬ (([] : List Nat) ≠ []) := by
  constructor
  · rfl
  · simp

-- axiom footprint
#print axioms msl_fmz_erdos400_campaign_001_R002_L1_a2r4
