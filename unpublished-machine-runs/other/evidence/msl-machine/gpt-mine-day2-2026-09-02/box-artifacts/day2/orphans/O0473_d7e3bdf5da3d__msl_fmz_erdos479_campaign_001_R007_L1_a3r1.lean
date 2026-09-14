import Mathlib

set_option autoImplicit false



def checkLTE (a : Nat) : Bool :=
  let m := 2 ^ (3 ^ a) + 1
  (m % (3 ^ (a + 1)) == 0) && (m % (3 ^ (a + 2)) != 0)

def checkAll : Bool := checkLTE 1 && checkLTE 2 && checkLTE 3

theorem msl_fmz_erdos479_campaign_001_R007_L1_a3r1  : checkAll = true ∧ (checkLTE a = true → (2 ^ (3 ^ a) + 1) % 3 ^ (a + 1) = 0 ∧ (2 ^ (3 ^ a) + 1) % 3 ^ (a + 2) ≠ 0) := by decide

-- axiom footprint
#print axioms checkLTE
#print axioms checkAll
#print axioms msl_fmz_erdos479_campaign_001_R007_L1_a3r1
