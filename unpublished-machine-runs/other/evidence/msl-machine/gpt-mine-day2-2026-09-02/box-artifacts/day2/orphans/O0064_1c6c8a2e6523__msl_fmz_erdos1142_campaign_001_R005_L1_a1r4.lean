import Mathlib

set_option autoImplicit false



-- no auxiliary definitions

theorem msl_fmz_erdos1142_campaign_001_R005_L1_a1r4  : ∀ k : ℕ, 3 ≤ k → ¬ Nat.Prime (2 * k - 2) := by
  intro k hk hp
  have hlt : 2 < 2 * k - 2 := by
    omega
  have hdiv : 2 ∣ 2 * k - 2 := by
    refine ⟨k - 1, ?_⟩
    omega
  have hone : 2 = 1 := by
    apply (Nat.prime_def_lt.mp hp).2 2 hlt
    exact hdiv
  omega

-- axiom footprint
#print axioms msl_fmz_erdos1142_campaign_001_R005_L1_a1r4
