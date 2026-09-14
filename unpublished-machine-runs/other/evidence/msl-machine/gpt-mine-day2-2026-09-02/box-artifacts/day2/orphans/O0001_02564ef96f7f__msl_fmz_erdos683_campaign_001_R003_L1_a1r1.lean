import Mathlib

set_option autoImplicit false


def fifthRootCeil (k : Nat) : Nat :=
  let rec go (r : Nat) : Nat := if (r+1)*(r+1)*(r+1)*(r+1)*(r+1) <= k then go (r+1) else r
  go 0

def lpf (m : Nat) : Nat :=
  if m <= 1 then 0 else
  let rec go (p : Nat) (m : Nat) : Nat :=
    if p * p > m then m else
    if m % p == 0 then go p (m / p) else go (p+1) m
  go 2 m

def binom (n k : Nat) : Nat :=
  (List.range (k+1)).foldl (fun acc i => acc * (n - i) / (i + 1)) 1

def boundAt (n k : Nat) : Nat := min (n - k + 1) (fifthRootCeil k)

def checkPair (n k : Nat) : Bool := lpf (binom n k) >= boundAt n k

def checkAll : Bool :=
  (List.range 100).all fun i =>
    let n := i + 1
    (List.range n).all fun j =>
      let k := j + 1
      checkPair n k

def checkTight : Bool :=
  checkPair 10 3 == false ∧ lpf (binom 10 3) == boundAt 10 3
  ∧ lpf (binom 22 4) == boundAt 22 4
  ∧ lpf (binom 27 5) == boundAt 27 5

def checkL1 : Bool := checkAll && checkTight

theorem msl_fmz_erdos683_campaign_001_R003_L1_a1r1  : checkL1 = true := by native_decide

-- axiom footprint
#print axioms fifthRootCeil
#print axioms lpf
#print axioms binom
#print axioms boundAt
#print axioms checkPair
#print axioms checkAll
#print axioms checkTight
#print axioms checkL1
#print axioms msl_fmz_erdos683_campaign_001_R003_L1_a1r1
