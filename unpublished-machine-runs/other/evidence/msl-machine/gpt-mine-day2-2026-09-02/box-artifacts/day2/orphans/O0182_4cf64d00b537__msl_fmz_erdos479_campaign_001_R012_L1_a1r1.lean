import Mathlib

set_option autoImplicit false


def isEven (n : Nat) : Bool := n % 2 == 0
def isOddK (k : Int) : Bool := k % 2 != 0
def twoPow (n : Nat) : Nat := 2 ^ n
/-- For even n and odd integer k, 2^n - k is odd, hence no even n divides 2^n - k. Checked over the decidable range n in [2, bound], k in the given odd list, using exact Nat arithmetic (2^n - k represented as 2^n + |k| when negative, since parity of 2^n - k equals parity of 2^n + k). -/
def parityOk (n : Nat) (k : Int) : Bool :=
  let pk := if k >= 0 then Int.toNat k else Int.toNat (-k)
  (twoPow n + pk) % 2 == 1

def checkL1 (bound : Nat) (ks : List Int) : Bool :=
  (List.range (bound - 1)).all fun i =>
    let n := i + 2
    isEven n && (ks.all fun k => isOddK k && parityOk n k)

def L1check : Bool :=
  checkL1 10000 [-3, -5, -7, 3, 5, 7]

theorem msl_fmz_erdos479_campaign_001_R012_L1_a1r1  : L1check = true := by native_decide

-- axiom footprint
#print axioms isEven
#print axioms isOddK
#print axioms twoPow
#print axioms parityOk
#print axioms checkL1
#print axioms L1check
#print axioms msl_fmz_erdos479_campaign_001_R012_L1_a1r1
