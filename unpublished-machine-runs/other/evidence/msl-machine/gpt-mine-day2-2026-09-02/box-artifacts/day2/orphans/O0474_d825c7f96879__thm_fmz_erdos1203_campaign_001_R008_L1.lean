import Mathlib

set_option autoImplicit false



-- no auxiliary definitions

theorem msl_fmz_erdos1203_campaign_001_R008_L1  : ∀ n : ℕ, (∑ k in Finset.range (n + 1), k) = n * (n + 1) / 2 := by
  intro n
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using Nat.sum_range_id (n + 1)

-- axiom footprint
#print axioms msl_fmz_erdos1203_campaign_001_R008_L1
