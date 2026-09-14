import Mathlib

set_option autoImplicit false


def primes11 : List Nat := [2, 3, 5, 7, 11]
def primes13 : List Nat := [2, 3, 5, 7, 11, 13]

def diffCovered (n : Nat) (ps : List Nat) : Bool :=
  ps.any (fun q1 => ps.any (fun q2 => q1 > q2 && q1 - q2 == n))

/- Exact residual-sign verifier, integer arithmetic only, no float paths.
   Branch TRUE : even n = 8 IS a difference of two primes <= 11 (11 - 3).
   Branch FALSE: even n = 12 is NOT a difference of two primes <= 13
                 (exhaustive over the list, fail-closed: `any` defaults false). -/
def verifierSigns : Bool :=
  diffCovered 8 primes11 && !(diffCovered 12 primes13)

theorem msl_fmz_erdos17_campaign_001_R002_L1  : verifierSigns = true := by decide

-- axiom footprint
#print axioms primes11
#print axioms primes13
#print axioms diffCovered
#print axioms verifierSigns
#print axioms msl_fmz_erdos17_campaign_001_R002_L1
