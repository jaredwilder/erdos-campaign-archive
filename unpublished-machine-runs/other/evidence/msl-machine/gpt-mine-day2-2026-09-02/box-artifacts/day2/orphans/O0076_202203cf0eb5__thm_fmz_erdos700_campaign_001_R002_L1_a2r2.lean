import Mathlib

set_option autoImplicit false



-- no auxiliary definitions

theorem msl_fmz_erdos700_campaign_001_R002_L1_a2r2  : ∀ n : ℕ, (∑ i in Finset.range n, (((i + 1 : ℕ) : ℤ) - (i : ℤ))) = (n : ℤ) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [Nat.cast_add, Nat.cast_one]
      ring

-- axiom footprint
#print axioms msl_fmz_erdos700_campaign_001_R002_L1_a2r2
