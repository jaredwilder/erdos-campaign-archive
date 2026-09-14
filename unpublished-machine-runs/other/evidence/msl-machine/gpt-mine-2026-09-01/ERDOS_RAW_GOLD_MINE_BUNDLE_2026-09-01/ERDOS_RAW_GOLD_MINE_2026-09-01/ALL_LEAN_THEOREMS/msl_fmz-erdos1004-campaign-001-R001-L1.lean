import Mathlib

set_option autoImplicit false

None

theorem msl_fmz_erdos1004_campaign_001_R001_L1  : ∀ n : ℕ, (∑ k in Finset.range n, k) = n * (n - 1) / 2 := by
  intro n
  simpa using Nat.sum_range_id n
