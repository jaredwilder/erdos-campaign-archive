import Mathlib

set_option autoImplicit false


def inB (m : Nat) : Bool :=
  not (m % 2 == 1) && not (m % 3 == 0)

def periodCheck (bound : Nat) : Bool :=
  (List.range bound).all (fun m => inB m == inB (m + 6))

def check : Bool :=
  periodCheck 48

theorem msl_fmz_erdos486_campaign_001_R005_L1  : check = true := by decide

-- axiom footprint
#print axioms inB
#print axioms periodCheck
#print axioms check
#print axioms msl_fmz_erdos486_campaign_001_R005_L1
