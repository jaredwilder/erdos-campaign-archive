import Mathlib

set_option autoImplicit false


def isPrime (n : Nat) : Bool :=
  n ≥ 2 && (List.range (n - 1)).all (fun d => d < 2 || n % (d + 1) != 0)

def primesUpTo (N : Nat) : List Nat :=
  (List.range (N + 1)).filter isPrime

/-- The residue-class condition for one AP: first term a, difference d, length k.
    Every prime q ≤ k with q ∤ a must divide d. -/
def okPair (k a d : Nat) (ps : List Nat) : Bool :=
  (primesUpTo k).all (fun q => a % q == 0 || d % q == 0)

/-- Decidable, total check: every length-k AP of primes with terms in [2, N]
    satisfies the residue-class condition. -/
def checkResidueCondition (k N : Nat) : Bool :=
  let ps := primesUpTo N
  (List.range (N + 1)).all (fun a =>
    (List.range N).all (fun dv =>
      let d := dv + 1
      let ap := (List.range k).map (fun i => a + i * d)
      !(ap.all (fun t => ps.contains t)) || okPair k a d ps))

theorem msl_fmz_erdos200_campaign_001_R005_L1  : checkResidueCondition 4 60 = true := by decide

-- axiom footprint
#print axioms isPrime
#print axioms primesUpTo
#print axioms okPair
#print axioms checkResidueCondition
#print axioms msl_fmz_erdos200_campaign_001_R005_L1
