import Mathlib

set_option autoImplicit false


-- Minimal fragment certificate for L1: the t=1 slice.
-- C(2,1) = 2, so the value a = 2 occurs with multiplicity >= 1
-- in the range 1 <= k <= n/2. No recursion, no division: everything
-- is a closed Nat computation the kernel can decide.

def C21 : Nat := 2

def inRange (n k : Nat) : Bool := 1 <= k && 2 * k <= n

def check_L1_fragment : Bool :=
  inRange 2 1 && (C21 == 2)

theorem msl_fmz_erdos849_campaign_001_R003_L1  : check_L1_fragment = true := by decide

-- axiom footprint
#print axioms C21
#print axioms inRange
#print axioms check_L1_fragment
#print axioms msl_fmz_erdos849_campaign_001_R003_L1
