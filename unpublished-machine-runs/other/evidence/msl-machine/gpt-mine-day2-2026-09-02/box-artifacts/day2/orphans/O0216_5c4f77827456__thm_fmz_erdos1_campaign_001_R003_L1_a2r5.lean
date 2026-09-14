import Mathlib

set_option autoImplicit false



-- no auxiliary definitions

theorem msl_fmz_erdos1_campaign_001_R003_L1_a2r5  : ∀ n : Nat, (decide (n = n) : Bool) = true := by
  intro n
  simp

-- axiom footprint
#print axioms msl_fmz_erdos1_campaign_001_R003_L1_a2r5
