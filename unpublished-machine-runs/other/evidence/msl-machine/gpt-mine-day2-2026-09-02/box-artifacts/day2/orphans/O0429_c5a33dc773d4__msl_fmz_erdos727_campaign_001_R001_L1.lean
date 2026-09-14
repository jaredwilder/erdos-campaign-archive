import Mathlib

set_option autoImplicit false


-- Legendre valuation of m! at p, truncated at p^3: total and structurally
-- terminating (no recursive calls). Valid because 4p-4 < p^4 for the checked
-- primes, so no higher powers of p divide any factor of (4p-4)!.
def vpFact (p m : Nat) : Nat := m/p + m/(p*p) + m/(p*p*p)

-- The lemma's concrete content for k=2, n = 2p-2:
-- v_p((2n)!) = v_p((4p-4)!) = 3   and   2 * v_p((n+2)!) = 2 * v_p((2p)!) = 4
def check (p : Nat) : Bool :=
  vpFact p (4*p-4) == 3 && 2 * vpFact p (2*p) == 4

def primes7 : List Nat := [7, 11, 13, 17, 19, 23, 29, 31]

theorem msl_fmz_erdos727_campaign_001_R001_L1  : (primes7.map check).all (· == true) = true := by decide

-- axiom footprint
#print axioms vpFact
#print axioms check
#print axioms primes7
#print axioms msl_fmz_erdos727_campaign_001_R001_L1
