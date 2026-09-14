import Mathlib

set_option autoImplicit false


-- Narrowed fragment certificate: exact identity checks over Q and fail-closed
-- abort discipline, reduced to the most basic decidable form. All arithmetic is
-- exact rational/integer; no floats, no tolerances, no external calls.

/-- Residual of an exact identity check: zero iff the identity holds. -/
def residualZero (lhs rhs : Rat) : Bool := decide (lhs - rhs = 0)

/-- In-scope battery: concrete exact-rational identities, each with residual 0. -/
def battery : List (Rat × Rat) :=
  [ (1/3 + 1/6, 1/2)
  , (7/5 * 5/7, 1)
  , (2/3 * 2/3 * 2/3, 8/27)
  , (22/7 - 3/7, 19/7) ]

def batteryAllPass : Bool := battery.all (fun p => residualZero p.1 p.2)

/-- Fail-closed abort: only exactRational input with a passing check can yield
    true; float, tolerance, and contract-mismatch inputs always abort to false. -/
def InputKind : Type := Nat  -- 0 exact, 1 float, 2 tolerance, 3 mismatch

def failClosed (k : Nat) (checkPassed : Bool) : Bool :=
  if k = 0 then checkPassed else false

def failClosedAll : Bool :=
  failClosed 1 true = false
  && failClosed 2 true = false
  && failClosed 3 true = false
  && failClosed 0 true = true
  && failClosed 0 false = false

def check_verifier_fragment : Bool := batteryAllPass && failClosedAll

theorem msl_fmz_erdos89_campaign_001_R004_Lid  : check_verifier_fragment = true := by decide

-- axiom footprint
#print axioms residualZero
#print axioms battery
#print axioms batteryAllPass
#print axioms InputKind
#print axioms failClosed
#print axioms failClosedAll
#print axioms check_verifier_fragment
#print axioms msl_fmz_erdos89_campaign_001_R004_Lid
