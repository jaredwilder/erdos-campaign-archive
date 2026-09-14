import Mathlib

set_option autoImplicit false


def isPrime (n : Nat) : Bool :=
  if n < 2 then false else (List.range (n - 2) |>.all (fun d => n % (d + 2) != 0))

def isGood (n : Nat) : Bool :=
  (List.range n |>.filter (fun k => 1 < k) |>.filter (fun k => 2 ^ k < n))
  |>.all (fun k => isPrime (n - 2 ^ k))

def check_lemma : Bool := isGood 4 && !isGood 5

theorem msl_fmz_erdos1142_campaign_001_R003_L1  : check_lemma = true := by decide

-- axiom footprint
#print axioms isPrime
#print axioms isGood
#print axioms check_lemma
#print axioms msl_fmz_erdos1142_campaign_001_R003_L1
