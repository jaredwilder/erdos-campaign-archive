import Mathlib

set_option autoImplicit false



-- no auxiliary definitions

theorem msl_fmz_erdos1038_campaign_001_R001_L1_a2r5  : ∀ n : Nat, n % 2 < 2 := by
  intro n
  exact Nat.mod_lt n (by decide)

-- axiom footprint
#print axioms msl_fmz_erdos1038_campaign_001_R001_L1_a2r5
