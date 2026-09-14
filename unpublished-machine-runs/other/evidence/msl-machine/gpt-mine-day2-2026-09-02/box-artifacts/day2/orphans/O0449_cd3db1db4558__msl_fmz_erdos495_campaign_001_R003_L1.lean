import Mathlib

set_option autoImplicit false


-- ||n*a/b|| scaled by b, exact integer arithmetic, b > 0
def normQ (n a b : Nat) : Nat :=
  let r := (n * a) % b
  min r (b - r)

-- alpha = beta = 1/2: n = 2 gives n*||n*alpha||*||n*beta|| = 0 exactly
def checkA : Bool := normQ 2 1 2 == 0

-- alpha = 3/5, beta = 4/5: n = 1 gives 1 * (2/5) * (1/5) = 2/25 < 1/25? no;
-- n = 2 gives 2 * (1/5) * (3/5) = 6/25; n = 3 gives 3 * (4/5)*(2/5) = 24/25;
-- n = 4 gives 4 * (2/5)*(1/5) = 8/25; n = 5 gives 0 exactly.
def checkB : Bool := normQ 5 3 5 == 0 && normQ 5 4 5 == 0

def check : Bool := checkA && checkB

theorem msl_fmz_erdos495_campaign_001_R003_L1  : check = true := by decide

-- axiom footprint
#print axioms normQ
#print axioms checkA
#print axioms checkB
#print axioms check
#print axioms msl_fmz_erdos495_campaign_001_R003_L1
