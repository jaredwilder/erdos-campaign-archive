import Mathlib

set_option autoImplicit false



def S : Nat → ℚ
  | 0 => 0
  | n+1 => S n + 1/(((n:ℚ)+1))^2

def check (n : Nat) : Bool := decide (S n < 2 - 1/((n:ℚ)))

def allChecks (N : Nat) : Bool := (List.range N).all (fun k => check (k+1))

theorem msl_fmz_erdos414_campaign_001_R001_L1  : allChecks 100 = true := by native_decide

-- axiom footprint
#print axioms S
#print axioms check
#print axioms allChecks
#print axioms msl_fmz_erdos414_campaign_001_R001_L1
