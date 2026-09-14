import Mathlib

set_option autoImplicit false



-- no auxiliary definitions

theorem msl_fmz_erdos289_campaign_001_R006_L1  : ∀ R B : ℚ, (0 ≤ B → (R ^ 2 ≤ B ^ 2 ↔ |R| ≤ B)) ∧ (B < 0 → ¬(|R| ≤ B)) := by
  intro R B
  constructor
  · intro hB
    constructor
    · intro hsq
      rcases le_total 0 R with hR | hR
      · rw [abs_of_nonneg hR]
        nlinarith
      · rw [abs_of_nonpos hR]
        nlinarith
    · intro habs
      rcases le_total 0 R with hR | hR
      · rw [abs_of_nonneg hR] at habs
        nlinarith
      · rw [abs_of_nonpos hR] at habs
        nlinarith
  · intro hB hbound
    exact (not_le_of_gt hB) (le_trans (abs_nonneg R) hbound)

-- axiom footprint
#print axioms msl_fmz_erdos289_campaign_001_R006_L1
