import Mathlib

set_option autoImplicit false



def selfCheck (n : Nat) : Bool := n == n

theorem msl_fmz_erdos1_campaign_001_R003_L1_a2r6  : ∀ n : Nat, selfCheck n = true := by
  intro n
  simp [selfCheck]

-- axiom footprint
#print axioms selfCheck
#print axioms msl_fmz_erdos1_campaign_001_R003_L1_a2r6
