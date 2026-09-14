import Mathlib

set_option autoImplicit false



def check_identity (bound : Nat) : Bool :=
  (List.range bound).all fun n =>
    2 * Nat.choose (2 * n + 1) n == Nat.choose (2 * n + 2) (n + 1)

def check_all_even (bound : Nat) : Bool :=
  (List.range bound).all fun n =>
    Nat.choose (2 * n + 2) (n + 1) % 2 == 0

theorem msl_fmz_erdos730_campaign_001_R005_L1  : check_identity 40 = true ∧ check_all_even 40 = true := by decide

-- axiom footprint
#print axioms check_identity
#print axioms check_all_even
#print axioms msl_fmz_erdos730_campaign_001_R005_L1
