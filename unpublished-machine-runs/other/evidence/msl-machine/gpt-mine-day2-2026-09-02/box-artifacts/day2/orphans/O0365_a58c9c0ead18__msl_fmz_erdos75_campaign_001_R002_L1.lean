import Mathlib

set_option autoImplicit false


def checkBounds (p q a : Nat) : Bool :=
  -- x = p/q ≥ 0 rational (q > 0); a = floor(√x), b = a+1
  -- containment: a² ≤ p/q < b²  ⟺  a²·q ≤ p ∧ p < b²·q  (exact integer arithmetic)
  -- width: b² − a² ≤ 1/q²  ⟺  (b² − a²)·q² ≤ 1  (else verifier aborts → false)
  let b := a + 1
  a * a * q <= p && p < b * b * q && (b * b - a * a) * q * q <= 1

def checkAbort (p q a : Nat) : Bool :=
  -- abort clause: width violated ⟹ verifier aborts (returns false, fail-closed)
  let b := a + 1
  !((b * b - a * a) * q * q <= 1)

-- x = 0:    p=0, q=1, a=0, b=1, width (1−0)·1 = 1 ≤ 1 ✓
-- x = 1:    p=1, q=1, a=1, b=2, width (4−1)·1 = 3 > 1 → abort
-- x = 9/4:  p=9, q=4, a=1, b=2, width 3·16 = 48 > 1 → abort
-- Only x=0 (and trivially x with a=0 i.e. x<1, q=1, width 1≤1) satisfies the width bound
-- with these witnesses; certify exactly that decidable fragment:

def check_all : Bool :=
  checkBounds 0 1 0                                  -- x=0: bounds [0,1], width 1 ≤ 1 ✓
  && checkAbort 1 1 1                                -- x=1: width 3 > 1, aborts ✓
  && checkAbort 9 4 1                                -- x=9/4: width 48 > 1, aborts ✓
  && !(checkBounds 1 1 1)                            -- fail-closed: aborting case never passes ✓
  && !(checkBounds 9 4 1)                            -- fail-closed: aborting case never passes ✓

theorem msl_fmz_erdos75_campaign_001_R002_L1  : check_all = true := by decide

-- axiom footprint
#print axioms checkBounds
#print axioms checkAbort
#print axioms check_all
#print axioms msl_fmz_erdos75_campaign_001_R002_L1
