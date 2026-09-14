import Mathlib

set_option autoImplicit false



-- no auxiliary definitions

theorem msl_fmz_erdos1038_campaign_001_R001_L1_a2r4  : ∀ n : Nat, n % 2 = 0 ∨ n % 2 = 1 := by
  intro n
  have h : n % 2 < 2 := Nat.mod_lt n (by decide)
  omega

-- axiom footprint
#print axioms msl_fmz_erdos1038_campaign_001_R001_L1_a2r4
