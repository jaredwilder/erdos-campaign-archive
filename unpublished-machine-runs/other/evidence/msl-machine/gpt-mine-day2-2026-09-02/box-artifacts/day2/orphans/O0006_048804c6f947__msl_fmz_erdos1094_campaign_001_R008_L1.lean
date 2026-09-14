import Mathlib

set_option autoImplicit false



namespace Erdos1094L1

/-- Standing lemma L1 in full: Sylvester's theorem (1892) — for 0 < k and 2k ≤ n,
binomial(n,k) has a prime factor greater than k. -/
def LemmaL1 : Prop :=
  ∀ n k : ℕ, 0 < k → 2 * k ≤ n → ∃ p : ℕ, Nat.Prime p ∧ k < p ∧ p ∣ n.choose k

end Erdos1094L1

theorem msl_fmz_erdos1094_campaign_001_R008_L1  : Erdos1094L1.LemmaL1 := by
  intro n k hk hnk
  exact Nat.sylvester n k hk hnk

-- axiom footprint
#print axioms Erdos1094L1.LemmaL1
#print axioms msl_fmz_erdos1094_campaign_001_R008_L1
