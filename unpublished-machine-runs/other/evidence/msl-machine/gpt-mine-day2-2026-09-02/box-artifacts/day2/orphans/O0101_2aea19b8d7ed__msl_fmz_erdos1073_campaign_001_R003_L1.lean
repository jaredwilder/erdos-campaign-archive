import Mathlib

set_option autoImplicit false


def envelope (n : Nat) : Nat := n / 2 + n / 4 + 1
def check : Bool :=
  envelope 1000000 == 750001 &&
  envelope 1000000 > 10000 &&
  envelope 1000000 <= 1000000

theorem msl_fmz_erdos1073_campaign_001_R003_L1  : check = true := by decide

-- axiom footprint
#print axioms envelope
#print axioms check
#print axioms msl_fmz_erdos1073_campaign_001_R003_L1
