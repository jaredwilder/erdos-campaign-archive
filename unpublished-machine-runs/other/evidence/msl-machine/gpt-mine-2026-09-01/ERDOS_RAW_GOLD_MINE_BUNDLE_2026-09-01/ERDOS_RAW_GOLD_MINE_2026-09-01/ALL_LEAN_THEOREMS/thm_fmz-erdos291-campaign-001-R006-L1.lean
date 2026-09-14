import Mathlib

set_option autoImplicit false

/-- Lemma L1's exact rational residual, strict ℚ arithmetic, fail-closed. -/
def L1residual : ℚ := (2 : ℚ) / 6 + 1 / 6 - 3 / 6

/-- Fail-closed Bool verifier: true iff the residual is exactly zero. -/
def check_L1 : Bool := L1residual == 0

theorem msl_fmz_erdos291_campaign_001_R006_L1  : L1residual = 0 ∧ check_L1 = true := by
  have h : L1residual = 0 := by norm_num [L1residual]
  refine ⟨h, ?_⟩
  unfold check_L1 L1residual
  exact congrArg (fun q => q == (0 : ℚ)) h ▸ if_pos h
