import Mathlib

set_option autoImplicit false

def hornerEval (coeffs : List ℚ) (x : ℚ) : ℚ :=
  coeffs.foldl (fun acc a => acc * x + a) 0

def exactCheck (gate : Bool) (coeffs : List ℚ) (x b : ℚ) : Bool :=
  gate && decide (|hornerEval coeffs x| ≤ b)

theorem msl_fmz_erdos1054_campaign_001_R008_L1  : ∀ (gate : Bool) (coeffs : List ℚ) (x b : ℚ),
    exactCheck gate coeffs x b = true ↔
      gate = true ∧ |hornerEval coeffs x| ≤ b := by
  intro gate coeffs x b
  simp [exactCheck]
