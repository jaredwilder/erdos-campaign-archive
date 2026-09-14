import Mathlib

set_option autoImplicit false


def powMod (_b e m : Nat) : Nat :=
  match e with
  | 0 => 1 % m
  | e' + 1 => (powMod _b e' m * _b) % m

def fermatPrimes : List Nat := [5, 17, 257, 65537]

/-- p - 1 is a power of 2 for these primes, so 3 is a generator iff 3^((p-1)/2) ≢ 1 (mod p). -/
def isNonResidue (p : Nat) : Bool := powMod 3 ((p - 1) / 2) p != 1 % p

def checkFermatList : Bool :=
  (fermatPrimes.map isNonResidue).all (fun b => b == true)

theorem msl_fmz_erdos985_campaign_001_R005_L1  : checkFermatList = true := by native_decide

-- axiom footprint
#print axioms powMod
#print axioms fermatPrimes
#print axioms isNonResidue
#print axioms checkFermatList
#print axioms msl_fmz_erdos985_campaign_001_R005_L1
