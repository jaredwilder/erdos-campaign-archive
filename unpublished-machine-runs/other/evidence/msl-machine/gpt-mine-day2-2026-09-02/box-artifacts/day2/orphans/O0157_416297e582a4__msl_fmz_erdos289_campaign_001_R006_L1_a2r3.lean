import Mathlib

set_option autoImplicit false



-- no auxiliary definitions

theorem msl_fmz_erdos289_campaign_001_R006_L1_a2r3  : ∀ R B : ℚ, (0 ≤ B ∧ R ^ 2 ≤ B ^ 2) ↔ (0 ≤ B ∧ |R| ≤ B) := by
  intro R B
  constructor
  · rintro ⟨hB, hsq⟩
    refine ⟨hB, ?_⟩
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (R - B), sq_nonneg (R + B)]
  · rintro ⟨hB, habs⟩
    refine ⟨hB, ?_⟩
    rw [abs_le] at habs
    rcases habs with ⟨hneg, hpos⟩
    nlinarith [sq_nonneg (R - B), sq_nonneg (R + B)]

-- axiom footprint
#print axioms msl_fmz_erdos289_campaign_001_R006_L1_a2r3
