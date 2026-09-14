import Mathlib

set_option autoImplicit false



def rational_comparison : Prop := ∀ (a b c d : ℚ), 0 < b → 0 < d → (a / b < c / d ↔ a * d < c * b)

theorem msl_fmz_erdos1199_campaign_001_R003_L1  : rational_comparison := by
  intro a b c d hb hd
  exact (div_lt_div_iff₀ hb hd)

-- axiom footprint
#print axioms rational_comparison
#print axioms msl_fmz_erdos1199_campaign_001_R003_L1
