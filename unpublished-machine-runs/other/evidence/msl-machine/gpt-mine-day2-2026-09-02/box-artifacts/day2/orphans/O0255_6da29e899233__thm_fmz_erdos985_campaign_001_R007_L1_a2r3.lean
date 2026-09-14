import Mathlib

set_option autoImplicit false



-- no auxiliary definitions

theorem msl_fmz_erdos985_campaign_001_R007_L1_a2r3  : ∀ n : Nat, n ≤ 50 → (∑ k in Finset.range (n + 1), k ^ 3) = (n * (n + 1) / 2) ^ 2 := by
  intro n hn
  interval_cases n <;> decide

-- axiom footprint
#print axioms msl_fmz_erdos985_campaign_001_R007_L1_a2r3
