import Mathlib

set_option autoImplicit false


def check_lemma_L1 : Bool :=
  -- |22/7| < 3143/1000 with positive numerators resolves to the exact integer cross-check 22 * 1000 < 7 * 3143.
  -- Computed exactly over Nat: 22 * 1000 = 22000, 7 * 3143 = 22001, so the check is strict and passes.
  22 * 1000 < 7 * 3143

def check_sign_resolution : Bool :=
  -- Both sides are positive naturals, so no sign case is unresolved: the absolute-value inequality
  -- |22/7| < 3143/1000 is equivalent to 22 * 1000 < 7 * 3143, and 22 * 1000 < 7 * 3143 is a Bool.
  decide (22 * 1000 < 7 * 3143)

theorem msl_fmz_erdos985_campaign_001_R001_L1  : check_lemma_L1 = true ∧ check_sign_resolution = true := by decide

-- axiom footprint
#print axioms check_lemma_L1
#print axioms check_sign_resolution
#print axioms msl_fmz_erdos985_campaign_001_R001_L1
