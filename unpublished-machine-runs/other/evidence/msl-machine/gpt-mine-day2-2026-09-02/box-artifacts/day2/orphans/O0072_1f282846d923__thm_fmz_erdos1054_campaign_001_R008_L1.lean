import Mathlib

set_option autoImplicit false



def exactCheck (q b : ℚ) : Bool := decide (|q| ≤ b)

theorem msl_fmz_erdos1054_campaign_001_R008_L1  : ∀ q b : ℚ, exactCheck q b = true ↔ |q| ≤ b := by
  intro q b
  simp only [exactCheck, decide_eq_true_eq]

-- axiom footprint
#print axioms exactCheck
#print axioms msl_fmz_erdos1054_campaign_001_R008_L1
