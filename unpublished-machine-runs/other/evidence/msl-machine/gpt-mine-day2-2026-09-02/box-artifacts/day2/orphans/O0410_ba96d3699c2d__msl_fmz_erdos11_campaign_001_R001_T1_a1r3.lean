import Mathlib

set_option autoImplicit false



def isSqfree : Nat → Bool
  | 0 => false | 1 => true
  | n+2 =>
    let k := n+2
    (List.range (k/2+1)).all fun d =>
      d < 2 ∨ ¬(d*d ∣ k)

def hasDecomp (n : Nat) : Bool :=
  (List.range (Nat.log2 n + 1)).any fun l =>
    2^l ≤ n ∧ isSqfree (n - 2^l)

def witnessCandidate (n : Nat) : Bool :=
  Odd n ∧ 1 < n ∧ ¬ hasDecomp n

def searchRange : List Nat :=
  (List.range 64).filter witnessCandidate

theorem msl_fmz_erdos11_campaign_001_R001_T1_a1r3  : searchRange = [] := by decide

-- axiom footprint
#print axioms isSqfree
#print axioms hasDecomp
#print axioms witnessCandidate
#print axioms searchRange
#print axioms msl_fmz_erdos11_campaign_001_R001_T1_a1r3
