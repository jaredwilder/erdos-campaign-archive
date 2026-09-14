import Mathlib

set_option autoImplicit false

-- no auxiliary definitions

theorem msl_fmz_erdos289_campaign_001_R006_L1  : ∀ R B : ℚ, (R ^ 2 ≤ B ^ 2 ∧ 0 ≤ B) ↔ |R| ≤ B := by
  intro R B
  by_cases hR : 0 ≤ R
  · rw [abs_of_nonneg hR]
    constructor
    · intro h
      nlinarith
    · intro h
      constructor
      · nlinarith
      · exact le_trans hR h
  · have hR' : R ≤ 0 := le_of_not_ge hR
    rw [abs_of_nonpos hR']
    constructor
    · intro h
      nlinarith
    · intro h
      constructor
      · nlinarith
      · nlinarith
