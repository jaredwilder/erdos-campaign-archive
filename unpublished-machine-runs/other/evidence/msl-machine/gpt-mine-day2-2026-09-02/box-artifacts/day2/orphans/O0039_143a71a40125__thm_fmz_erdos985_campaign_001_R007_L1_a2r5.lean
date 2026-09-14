import Mathlib

set_option autoImplicit false



-- no auxiliary definitions

theorem msl_fmz_erdos985_campaign_001_R007_L1_a2r5  : ∀ n : ℕ, (∑ k in Finset.range n, k ^ 3) = (n * (n - 1) / 2) ^ 2 := by
  intro n
  simpa using Finset.sum_range_id_cube n

-- axiom footprint
#print axioms msl_fmz_erdos985_campaign_001_R007_L1_a2r5
