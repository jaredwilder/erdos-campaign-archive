import Mathlib

set_option autoImplicit false


def ceilK75 (k : Nat) : Nat :=
  -- ceil(k^{7/5}) = least r with r^5 >= k^7, exact integer arithmetic
  ((List.range (k*k*k*k*k*k*k + 2)).find? (fun r => k^7 <= r^5)).getD 0

def lpf (m : Nat) : Nat :=
  -- largest prime factor by exact trial division over divisors
  ((List.range (m + 1)).filter Nat.Prime).filter (fun p => m % p == 0)
    |>.foldr max 0

def binom (n k : Nat) : Nat :=
  (List.range (k+1)).foldl (fun acc i => acc * (n - i) / (i + 1)) 1

def boundAt (n k : Nat) : Nat := min (n - k + 1) (ceilK75 k)

def checkPair (n k : Nat) : Bool := lpf (binom n k) >= boundAt n k

def checkAll : Bool :=
  (List.range 15).all fun i =>
    let n := i + 1
    (List.range n).all fun j =>
      let k := j + 1
      checkPair n k

def checkL1 : Bool := checkAll

theorem msl_fmz_erdos683_campaign_001_R003_L1_a1r2  : checkL1 = true := by native_decide

-- axiom footprint
#print axioms ceilK75
#print axioms lpf
#print axioms binom
#print axioms boundAt
#print axioms checkPair
#print axioms checkAll
#print axioms checkL1
#print axioms msl_fmz_erdos683_campaign_001_R003_L1_a1r2
