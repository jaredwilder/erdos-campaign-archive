import Mathlib

set_option autoImplicit false


def distinctPrimeFactors (n : Nat) : List Nat := (List.range (n+1)).filter (fun p => Nat.Prime p && p ∣ n)
def omega (n : Nat) : Nat := (distinctPrimeFactors n).length
def pow2 : Nat → Nat | 0 => 1 | (a+1) => 2 * pow2 a
def check_k1 (N : Nat) : Bool := (List.range (N+1)).all (fun a => omega (pow2 a) == 1)

theorem msl_fmz_erdos890_campaign_001_R002_L1_a1r1  : check_k1 40 = true := by decide

-- axiom footprint
#print axioms distinctPrimeFactors
#print axioms omega
#print axioms pow2
#print axioms check_k1
#print axioms msl_fmz_erdos890_campaign_001_R002_L1_a1r1
