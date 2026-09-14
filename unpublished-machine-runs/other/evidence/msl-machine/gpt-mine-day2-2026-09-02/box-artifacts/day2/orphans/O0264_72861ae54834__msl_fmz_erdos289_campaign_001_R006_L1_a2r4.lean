import Mathlib

set_option autoImplicit false



def l1_statement : Prop := ∀ (R B : ℚ), 0 ≤ B → (R ^ 2 ≤ B ^ 2 ↔ |R| ≤ B)

theorem msl_fmz_erdos289_campaign_001_R006_L1_a2r4  : l1_statement := by
  intro R B hB
  constructor
  · intro h
    have h' : |R| ^ 2 ≤ B ^ 2 := by simpa [sq_abs] using h
    exact (sq_le_sq₀ (abs_nonneg R) hB).mp h'
  · intro h
    have h' : |R| ^ 2 ≤ B ^ 2 := (sq_le_sq₀ (abs_nonneg R) hB).mpr h
    simpa [sq_abs] using h'

-- axiom footprint
#print axioms l1_statement
#print axioms msl_fmz_erdos289_campaign_001_R006_L1_a2r4
