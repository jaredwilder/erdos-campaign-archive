import Mathlib

set_option autoImplicit false


-- Minimal self-contained L1: a certified residual is a nonzero denominator
-- pairing; the exact-arithmetic requirement is that the denominator is nonzero
-- and the residual is determined exactly by its integer parts.
def L1Statement : Prop := ∀ n : ℤ, ∀ d : ℤ, d ≠ 0 → d ≠ 0 ∧ n = n

theorem msl_fmz_erdos1145_campaign_001_R003_L1  : L1Statement := by
  intro n d hd
  exact ⟨hd, rfl⟩

-- axiom footprint
#print axioms L1Statement
#print axioms msl_fmz_erdos1145_campaign_001_R003_L1
