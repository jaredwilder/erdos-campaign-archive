import Mathlib

set_option autoImplicit false



-- a neutral stand-in for a published bound of the shape
-- S N <= C * N * log N, so the gate is exercised on the real shape.

axiom CloserSelftest_PlaceholderBound_NotACitation :
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N → (N : ℝ) ≤ C * (N : ℝ) * Real.log N

theorem msl_closer_selftest_lap  : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N → (N : ℝ) ≤ C * (N : ℝ) * (Real.log N) ^ 2 := by
  obtain ⟨C, hC, h⟩ := CloserSelftest_PlaceholderBound_NotACitation
  refine ⟨C, hC, fun N hN => ?_⟩
  have h3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hlog : (1 : ℝ) ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hpos]
    have := Real.exp_one_lt_d9
    linarith
  have hb := h N hN
  nlinarith [hb, hC, hpos, hlog, sq_nonneg (Real.log N)]

-- axiom footprint
#print axioms msl_closer_selftest_lap
