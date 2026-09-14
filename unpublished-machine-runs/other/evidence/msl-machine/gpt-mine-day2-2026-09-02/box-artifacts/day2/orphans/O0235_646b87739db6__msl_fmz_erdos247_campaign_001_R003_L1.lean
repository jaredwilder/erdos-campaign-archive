import Mathlib

set_option autoImplicit false



-- no auxiliary definitions

theorem msl_fmz_erdos247_campaign_001_R003_L1  : Real.sqrt (2 : ℝ) < (141 : ℝ) / 99 := by
  have hs : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := by
    rw [Real.sq_sqrt]
    norm_num
  have hq : 0 < (141 : ℝ) / 99 := by
    norm_num
  have hsq : (Real.sqrt (2 : ℝ)) ^ 2 < ((141 : ℝ) / 99) ^ 2 := by
    rw [hs2]
    norm_num
  nlinarith

-- axiom footprint
#print axioms msl_fmz_erdos247_campaign_001_R003_L1
