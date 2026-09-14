import Mathlib

set_option autoImplicit false



-- no auxiliary definitions

theorem msl_fmz_erdos295_campaign_001_R004_L1  : ((∀ t : ℚ, 0 ≤ t → (3 * (2 + t)^2 - 1 = 11 + 12 * t + 3 * t^2 ∧ 0 < 3 * (2 + t)^2 - 1)) ∧ 3 * (2 : ℚ)^2 - 1 = 11) := by
  constructor
  · intro t ht
    constructor
    · ring
    · calc
        0 < (11 : ℚ) := by norm_num
        _ ≤ 11 + 12 * t + 3 * t^2 := by
          have ht2 : 0 ≤ t^2 := sq_nonneg t
          nlinarith
        _ = 3 * (2 + t)^2 - 1 := by ring
  · norm_num

-- axiom footprint
#print axioms msl_fmz_erdos295_campaign_001_R004_L1
