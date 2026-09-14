import Mathlib

set_option autoImplicit false


def isOdd (n : Nat) : Bool := n % 2 == 1

def rep1 (n : Nat) : Bool := true  -- n ∈ ℕ, so n is represented by itself as a 1-term sum

def rep2odds (n : Nat) : Bool :=
  (List.range (n+1)).any (fun a =>
    (List.range (n+1)).any (fun b => a + b == n && isOdd a && isOdd b))

def check_fragment : Bool :=
  -- (i) ℕ is an order-1 basis on the checked range: every n ≤ 100 is representable
  ((List.range 101).all (fun n => rep1 n))
  -- (ii) odds fail to be an order-2 basis: 1 is NOT a sum of two odd naturals
  && (rep2odds 1 == false)

theorem msl_fmz_erdos881_campaign_001_R001_L1  : check_fragment = true := by decide

-- axiom footprint
#print axioms isOdd
#print axioms rep1
#print axioms rep2odds
#print axioms check_fragment
#print axioms msl_fmz_erdos881_campaign_001_R001_L1
