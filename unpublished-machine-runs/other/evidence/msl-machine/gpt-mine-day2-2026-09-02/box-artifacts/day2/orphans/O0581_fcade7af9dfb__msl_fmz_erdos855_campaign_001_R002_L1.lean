import Mathlib

set_option autoImplicit false


def oddSum : Nat → Nat
  | 0 => 0
  | (n+1) => oddSum n + (2*(n+1) - 1)

def checkRange : Nat → Bool
  | 0 => (oddSum 0 == 0*0)
  | (n+1) => checkRange n && (oddSum (n+1) == (n+1)*(n+1))

theorem msl_fmz_erdos855_campaign_001_R002_L1  : checkRange 60 = true := by decide

-- axiom footprint
#print axioms oddSum
#print axioms checkRange
#print axioms msl_fmz_erdos855_campaign_001_R002_L1
