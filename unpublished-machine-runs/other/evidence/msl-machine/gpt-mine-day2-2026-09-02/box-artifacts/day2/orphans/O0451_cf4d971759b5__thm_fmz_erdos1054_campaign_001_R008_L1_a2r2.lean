import Mathlib

set_option autoImplicit false



def horner : List ℚ → ℚ → ℚ
  | [], _ => 0
  | a :: rest, x => a + x * horner rest x

def exactCheck (gate : Bool) (coeffs : List ℚ) (x b : ℚ) : Bool :=
  if gate = true then
    if |horner coeffs x| ≤ b then true else false
  else
    false

theorem msl_fmz_erdos1054_campaign_001_R008_L1_a2r2  : ∀ (gate : Bool) (coeffs : List ℚ) (x b : ℚ), exactCheck gate coeffs x b = true ↔ gate = true ∧ |horner coeffs x| ≤ b := by
  intro gate coeffs x b
  cases gate <;> simp [exactCheck]

-- axiom footprint
#print axioms horner
#print axioms exactCheck
#print axioms msl_fmz_erdos1054_campaign_001_R008_L1_a2r2
