import Mathlib

set_option autoImplicit false


def tri (n : Nat) : Nat := (List.range (n+1)).foldl (· + ·) 0

def check_L1 (bound : Nat) : Bool :=
  (List.range (bound + 1)).all fun n =>
    tri n == n * (n + 1) / 2

theorem msl_fmz_erdos91_campaign_001_R001_L1  : check_L1 40 = true := by decide

-- axiom footprint
#print axioms tri
#print axioms check_L1
#print axioms msl_fmz_erdos91_campaign_001_R001_L1
