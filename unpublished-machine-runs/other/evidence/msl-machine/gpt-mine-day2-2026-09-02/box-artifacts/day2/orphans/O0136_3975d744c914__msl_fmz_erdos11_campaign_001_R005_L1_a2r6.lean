import Mathlib

set_option autoImplicit false



-- no auxiliary definitions

theorem msl_fmz_erdos11_campaign_001_R005_L1_a2r6  : ∃ k l : ℕ, Squarefree k ∧ 3 = k + 2 ^ l := by
  refine ⟨1, 1, ?_, ?_⟩
  · simp
  · norm_num

-- axiom footprint
#print axioms msl_fmz_erdos11_campaign_001_R005_L1_a2r6
